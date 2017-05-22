#!/bin/sh

for f in _lem/*.lem
do
  f=${f#_lem/}
  f=$1/${f%.lem}.ml
  sed -i"" -e "s/^(\* File \(\"[^\"]*\"\), line \([0-9]*\).*\*)/# \2 \1/" $f
done