#!/bin/bash
ulimit -Ss 49152
export OCAMLRUNPARAM=s=4M,i=32M,o=150

make

# append '--html' to goblint run to generate the 'result/' directory

# 433.milc benchmark: runexp -- each var is separate;  runcomb -- all vars together
# time ./goblint mytest/433.milc_comb.c --enable runexp  --enable exp.single-threaded --sets result none
time ./goblint mytest/433.milc_comb.c --enable runcomb --enable exp.single-threaded --sets result none

# lp linux char driver benchmark: runexp -- each var is separate;  runcomb -- all vars together
# time ./goblint mytest/lp.c   --enable runexp  --enable kernel --set mainfun "['lp_init_module']" --sets result none
# time ./goblint mytest/lp.c   --enable runcomb --enable kernel --set mainfun "['lp_init_module']" --sets result none 