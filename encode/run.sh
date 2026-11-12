#!/bin/bash
mkdir -p wcnf
output=./wcnf/$(basename $1 .cnf.xz)
NUMBERVARS=$(./encodeMaxAutarky $1 $output)
tmpfile=$(mktemp)
~/Bachelorprojekt/solvers/uwrmaxsat/build/release/bin/uwrmaxsat $output.wcnf > $tmpfile
./compareMaxAutarky $tmpfile $NUMBERVARS
rm $tmpfile