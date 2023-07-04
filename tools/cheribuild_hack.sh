#!/bin/bash

trap 'repair_dune' SIGINT

# GNU vs BSD
if sed --version 2>/dev/null 1>/dev/null; then
  MYSEDI="sed -i"
else
  MYSEDI="sed -i ''"
fi

function repair_dune() {
  $MYSEDI '/(dirs/s/ coq//' dune
}

function add_coq() {
  $MYSEDI 's/(dirs \([^)]*\))/(dirs \1 coq)/' dune
}

add_coq
eval $1
repair_dune
