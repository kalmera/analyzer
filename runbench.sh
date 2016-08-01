#!/bin/bash
ulimit -Ss 49152
export OCAMLRUNPARAM=s=4M,i=32M,o=150

make

# append '--html' to goblint run to generate the 'result/' directory

# 433.milc benchmark: runexp -- each var is separate;  runcomb -- all vars together
time ./goblint mytest/433.milc_comb.c --enable runexp  --enable exp.single-threaded --sets result none
time ./goblint mytest/433.milc_comb.c --enable runcomb --enable exp.single-threaded --sets result none

# 433.milc benchmark: runexp -- each var is separate;  runcomb -- all vars together
time ./goblint mytest/scx200_gpio.c   --enable runexp  --enable kernel --sets result none 
time ./goblint mytest/scx200_gpio.c   --enable runcomb --enable kernel --sets result none