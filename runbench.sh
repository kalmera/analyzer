#!/bin/bash
ulimit -Ss 49152
export OCAMLRUNPARAM=s=4M,i=32M,o=150

GOBLINTDIR="../morevars"

FILES="single-thread/433.milc_comb.c"

OUTFILE=$1

CMD="time $GOBLINTDIR/goblint --enable runexp --sets result none"

if [ -z "$OUTFILE" ]
then
  echo "Output file is not specified"
  exit 1
fi

date > $OUTFILE

for f in $FILES
do
  echo $f
  echo "" >> $OUTFILE
  echo "============================================================" >> $OUTFILE
  echo $f >> $OUTFILE
  ($CMD $f 2>&1) >> $OUTFILE
done


time ./goblint mytest/433.milc_comb.c --enable runexp --sets result none