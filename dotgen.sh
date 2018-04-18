#!/bin/sh

find * -iname 'dot_graph_*.dot' | xargs -I '$' neato -Tpng -O '$' 

convert dot_graph_*.dot.png graphs.pdf

rm ./dot_graph_*.dot.png
