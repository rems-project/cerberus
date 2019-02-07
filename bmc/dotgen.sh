#!/bin/sh

find * -iname 'graph_*.dot' | xargs -I '$' neato -Tpng -O '$' 

convert graph_*.dot.png graphs.pdf

rm ./graph_*.dot.png
