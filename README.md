# lnsim
Lightning Network Simulator

Edit lnsimtop.ml to simulate as many steps as you like.
One payment is attempted for each step.

To compile and run:
```
ocamlopt -o lnsim.cmx -c lnsim.ml
ocamlopt -o lnsimtop.cmx -c lnsimtop.ml
ocamlopt -o lnsimtop unix.cmxa lnsim.cmx lnsimtop.cmx
./lnsimtop
```
