let balance : (int * int,float * float) Hashtbl.t = Hashtbl.create 100000;;

let simulatedtime = ref 0;;

let routingfailed = ref 0;;
let midsizedpaymentroutingfailed = ref 0;;
let micropaymentroutingfailed = ref 0;;
let paymentattempted = ref 0;;
let midsizedpaymentattempted = ref 0;;
let micropaymentattempted = ref 0;;
let recentroutelensbig = Array.make 1000 0;;
let recenttotalfeesbig = Array.make 1000 0.0;;
let recenttotalfeespercentbig = Array.make 1000 0.0;;
let recentroutelensmid = Array.make 1000 0;;
let recenttotalfeesmid = Array.make 1000 0.0;;
let recenttotalfeespercentmid = Array.make 1000 0.0;;
let recentroutelensmicro = Array.make 1000 0;;
let recenttotalfeesmicro = Array.make 1000 0.0;;
let recenttotalfeespercentmicro = Array.make 1000 0.0;;
let recentcounterbig = ref 0;;
let recentcountermid = ref 0;;
let recentcountermicro = ref 0;;

exception Timeout;;
let timedout = ref false;;

let set_timer s =
  ignore (Sys.signal Sys.sigalrm (Sys.Signal_handle (fun signo -> timedout := true; raise Timeout)));
  ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = s });;

let adjtest : (int,unit) Hashtbl.t = Hashtbl.create 15;;

let n = ref 1 in for i = 1 to 7 do Hashtbl.add adjtest !n (); Hashtbl.add adjtest (10000000 - !n) (); n := !n * 10 done;;

let adjacent i j =
  if i > j then
    Hashtbl.mem adjtest (i - j)
  else
    Hashtbl.mem adjtest (j - i)

let getbalance (i,j) =
  let getbalance1 i j =
    try
      Hashtbl.find balance (i,j)
    with Not_found ->
      (0.01,0.01)
  in
  if i < j then
    getbalance1 i j
  else
    let (x,y) = getbalance1 j i in
    (y,x)

let setbalance (i,j) (x,y) =
  let setbalance1 i j x y =
    Hashtbl.replace balance (i,j) (x,y)
  in
  if i < j then
    setbalance1 i j x y
  else
    setbalance1 j i y x

exception InsufficientFunds

(*** fee for sending w from i via j, decided by j since this rebalances two of j's channels ***)
let routingfee i j w =
  let (x,y) = getbalance (i,j) in
  let fee =
    let c = j mod 11 in (*** 11 kinds of users with different fee policies ***)
    if c = 0 then
      0.00000001 (*** low fixed fee ***)
    else if c = 1 then
      0.0000001 (*** medium fixed fee ***)
    else if c = 2 then
      0.000001 (*** high fixed fees ***)
    else if c = 3 then (*** low percentage fee ***)
      w *. 0.000001
    else if c = 4 then (*** medium percentage fee ***)
      w *. 0.00001
    else if c = 5 then (*** high percentage fee ***)
      w *. 0.0001
    else (*** the rest make fees dependent on trying to make channels more balanced ***)
      let xy = x +. y in
      let py = y /. xy in (*** in [0,1]; the closer to 0, the happier y is to accept money from x; fee of p * w + m py + b where m is positive (low fees when py is small) ***)
      let (p,m,b) =
	if c = 6 then
	  (0.0,0.0000001,0.0)
	else if c = 7 then
	  (0.0000001,0.00000001,0.00000001)
	else if c = 8 then
	  (0.0,0.000001,-0.0000001)
	else if c = 9 then
	  (0.0000001,0.000002,-0.0000001)
	else
	  (0.000001,0.000004,-0.0000001)
      in
      w *. p +. m *. py +. b
  in
  if w +. fee > x then raise InsufficientFunds;
  (fee,x)

let approxdist i j =
  let dd k = min k (10 - k) in
  let approxdist1 i j =
    let d = ref 0 in
    let n = ref 1 in
    let ij = if i > j then i - j else j - i in
    for k = 1 to 7 do
      d := !d + (dd ((ij / !n) mod 10));
      n := 10 * !n
    done;
    !d
  in  
  min (approxdist1 i j) (approxdist1 j i)

let rec greedyroutes1 r i j w maxfee avoid =
  if r <= 0 then
    []
  else if i = j then
    [([],0.0)]
  else if adjacent i j then
    begin
      try
	let (fee,x) = routingfee i j w in
	if fee >= maxfee then raise InsufficientFunds;
	[([(i,j,fee,w +. fee)],fee)]
      with InsufficientFunds -> []
    end
  else
    let cands = ref [] in
    let addcandidate k =
      if not (List.mem k avoid) then
	try
	  let (fee,x) = routingfee i k w in
	  if fee >= maxfee then raise InsufficientFunds;
	  cands := (k,approxdist k j,fee,x)::!cands
	with InsufficientFunds -> ()
    in
    let n = ref 1 in
    for unused = 1 to 7 do
      addcandidate ((i + !n) mod 10000000);
      if i > !n then
	addcandidate (i - !n)
      else
	addcandidate (!n - i);
      n := 10 * !n
    done;
    let cands2 = List.sort (fun (k1,d1,fee1,_) (k2,d2,fee2,_) -> compare (fee1 +. 0.0001 *. float_of_int d1) (fee2 +. 0.0001 *. float_of_int d2)) !cands in
    greedyroutes2 r cands2 i j w maxfee avoid
and greedyroutes2 r cands i j w maxfee avoid =
  match cands with
  | [] -> []
  | (k,d,fee,x)::candsr ->
      let routes =
	List.map
	  (fun (route,totalfee) -> ((i,k,fee,w +. fee +. totalfee)::route,fee +. totalfee))
	  (List.filter (fun (route,totalfee) -> x >= w +. fee +. totalfee)
	     (greedyroutes1 r k j w (maxfee -. fee) (i::avoid)))
      in
      if List.length routes < r && not !timedout then
	begin
	  try
	    List.sort
	      (fun (_,totalfee1) (_,totalfee2) -> compare totalfee1 totalfee2)
	      (routes @ greedyroutes2 (int_of_float (float_of_int (r - List.length routes) /. 1.2)) candsr i j w maxfee avoid)
	  with Timeout -> routes
	end
      else
	routes
    
let greedyroutes i j w maxfee avoid =
  List.sort (fun (route1,totalfee1) (route2,totalfee2) -> compare totalfee1 totalfee2) (greedyroutes1 5 i j w maxfee avoid)

let greedyroute i j w maxfee avoid =
  let rec greedyroute_r iter avoid bestroute besttotalfee =
    if iter > 0 then
      begin
	match bestroute with
	| [] -> ([],besttotalfee) (*** should never happen ***)
	| (i1,j1,fee1,w1)::router ->
	    try
	      let worstnode = ref j1 in
	      let biggestfee = ref fee1 in
	      List.iter (fun (i2,j2,fee2,w2) -> if fee2 > !biggestfee then (biggestfee := fee2; worstnode := j2)) router;
	      let avoid = !worstnode::avoid in
	      match greedyroutes i j w besttotalfee avoid with
	      | [] -> (bestroute,besttotalfee)
	      | (route,totalfee)::_ -> greedyroute_r (iter-1) avoid route totalfee
	    with Timeout ->
	      (bestroute,besttotalfee)
      end
    else
      (bestroute,besttotalfee)
  in
  match greedyroutes i j w maxfee avoid with
  | [] -> raise Not_found
  | (route,totalfee)::_ -> greedyroute_r 2 avoid route totalfee

let greedyroute_timeout s i j w maxfee avoid =
  set_timer 0.1;
  let r = greedyroute i j w maxfee avoid in
  timedout := false;
  set_timer 0.0;
  r

let report () =
  let users : (int,unit) Hashtbl.t = Hashtbl.create 10000 in
  let userstouched = ref 0 in
  let channelstouched = ref 0 in
  let lowbalancechannels = ref 0 in
  let slightlyoutofbalancechannels = ref 0 in
  let veryoutofbalancechannels = ref 0 in
  Hashtbl.iter
    (fun (i,j) (x,y) ->
      if not (Hashtbl.mem users i) then (Hashtbl.add users i (); incr userstouched);
      if not (Hashtbl.mem users j) then (Hashtbl.add users j (); incr userstouched);
      incr channelstouched;
      if x < 0.001 || y < 0.001 then incr lowbalancechannels;
      let p = x /. (x +. y) in
      if p < 0.1 || p > 0.9 then
	if p < 0.01 || p > 0.99 then
	  incr veryoutofbalancechannels
	else
	  incr slightlyoutofbalancechannels)
    balance;
  Printf.printf "=============================\nTime: %d units\n" !simulatedtime;
  Printf.printf "Channels that have been used: %d\n" !channelstouched;
  Printf.printf "Users that have participated: %d\n" !userstouched;
  Printf.printf "Channels with a low balance (< 0.001 btc) on one side: %d\n" !lowbalancechannels;
  Printf.printf "Channels where one side has > 90%% of the balance: %d\n" !slightlyoutofbalancechannels;
  Printf.printf "Channels where one side has > 99%% of the balance: %d\n" !veryoutofbalancechannels;
  Printf.printf "Payments attempted: %d\n" !paymentattempted;
  Printf.printf "Routing failed: %d\n" !routingfailed;
  Printf.printf "Midsizedpayments attempted: %d\n" !midsizedpaymentattempted;
  Printf.printf "Routing failed for midsizedpayments: %d\n" !midsizedpaymentroutingfailed;
  Printf.printf "Micropayments attempted: %d\n" !micropaymentattempted;
  Printf.printf "Routing failed for micropayments: %d\n" !micropaymentroutingfailed;
  let reportfeesandlens recenttotalfees recenttotalfeespercent recentroutelens =
    let rtf = List.sort compare (Array.to_list recenttotalfees) in
    let rtfp = List.sort compare (Array.to_list recenttotalfeespercent) in
    Printf.printf "Average (mean) recent total fees: %f\nand as a percentage of the payment %f\n" ((List.fold_left (fun u v -> u +. v) 0.0 rtf) /. 1000.0) ((List.fold_left (fun u v -> u +. v) 0.0 rtfp) /. 1000.0);
    Printf.printf "Average (median) recent total fees: %f\nand as a percentage of the payment %f\n" (List.nth rtf 500) (List.nth rtfp 500);
    let rrl = List.sort compare (Array.to_list recentroutelens) in
    Printf.printf "Average recent lengths of routes (mean): %f and (median): %d\n" ((List.fold_left (fun u v -> u +. float_of_int v) 0.0 rrl) /. 1000.0) (List.nth rrl 500);
  in
  if !recentcounterbig >= 1000 then
    begin
      Printf.printf "* For big payments (0.001 - 0.009):\n";
      reportfeesandlens recenttotalfeesbig recenttotalfeespercentbig recentroutelensbig;
    end;
  if !recentcountermid >= 1000 then
    begin
      Printf.printf "* For midsize payments (0.00001 - 0.001):\n";
      reportfeesandlens recenttotalfeesmid recenttotalfeespercentmid recentroutelensmid;
    end;
  if !recentcountermicro >= 1000 then
    begin
      Printf.printf "* For micropayments (< 0.00001):\n";
      reportfeesandlens recenttotalfeesmicro recenttotalfeespercentmicro recentroutelensmicro;
    end;
  flush stdout;
  let f = open_out_bin ("state" ^ (string_of_int !simulatedtime)) in
  output_value f balance;
  close_out f

exception UncooperativeNode of int

let attempt_payment route i j w =
  List.iter
    (fun (k,l,fee,v) ->
      if Random.int 1000 = 0 then (*** simulate random failures of intermediate nodes, 0.1% of the time ***)
	if k = i || k = j then
	  if l = i || l = j then
	    ()
	  else
	    raise (UncooperativeNode(l))
	else
	  raise (UncooperativeNode(k));
      let (x,y) = getbalance (k,l) in
      if x < v then
	if k = i || k = j then
	  raise Not_found
	else
	  raise (UncooperativeNode(k)))
    route;
  List.iter
    (fun (k,l,fee,v) ->
      let (x,y) = getbalance (k,l) in
      setbalance (k,l) (x -. v,y +. v))
    route

let sim totime =
  let totalusers = 10000000 in
  let midsizedpaymentcutoff = 0.001 in
  let micropaymentcutoff = 0.00001 in
  while !simulatedtime < totime do
    incr simulatedtime;
    let i = Random.int totalusers in
    let j = Random.int totalusers in
    if not (i = j) then
      begin
	let w =
	  let rw = Random.int 3 in
	  if rw = 0 then
	    midsizedpaymentcutoff +. Random.float 0.008 (** "big" **)
	  else if rw = 1 then (** "medium" **)
	    (incr midsizedpaymentattempted;
	     micropaymentcutoff +. Random.float (midsizedpaymentcutoff -. micropaymentcutoff))
	  else (** "micro" **)
	    (incr micropaymentattempted;
	     Random.float micropaymentcutoff)
	in
	incr paymentattempted;
	try
	  let (route,totalfees) = greedyroute_timeout 1.0 i j w (max 0.00001 (w *. 0.05)) [] in
	  let tryroute = ref route in
	  let avoid = ref [] in
	  let retry = ref 5 in
	  let success = ref false in
	  while not !success && !retry > 0 do
	    try
	      attempt_payment !tryroute i j w;
	      let countrecent recentcounter recentroutelens recenttotalfees recenttotalfeespercent =
		recentroutelens.(!recentcounter mod 1000) <- List.length !tryroute;
		recenttotalfees.(!recentcounter mod 1000) <- totalfees;
		recenttotalfeespercent.(!recentcounter mod 1000) <- 100.0 *. (totalfees /. (w +. totalfees));
		incr recentcounter
	      in
	      if w < midsizedpaymentcutoff then
		if w < micropaymentcutoff then
		  countrecent recentcountermicro recentroutelensmicro recenttotalfeesmicro recenttotalfeespercentmicro
		else
		  countrecent recentcountermid recentroutelensmid recenttotalfeesmid recenttotalfeespercentmid
	      else
		countrecent recentcounterbig recentroutelensbig recenttotalfeesbig recenttotalfeespercentbig;
	      success := true
	    with UncooperativeNode(k) ->
	      avoid := k::!avoid;
	      let (route,totalfees) = greedyroute_timeout 1.0 i j w (max 0.00001 (w *. 0.05)) !avoid in
	      tryroute := route;
	      decr retry
	  done
	with
	| Not_found ->
	    incr routingfailed;
	    if w < midsizedpaymentcutoff then
	      if w < micropaymentcutoff then
		incr micropaymentroutingfailed
	      else
		incr midsizedpaymentroutingfailed
	| Timeout ->
	    timedout := false;
	    incr routingfailed;
	    if w < midsizedpaymentcutoff then
	      if w < micropaymentcutoff then
		incr micropaymentroutingfailed
	      else
		incr midsizedpaymentroutingfailed
      end
  done;
  report ()
