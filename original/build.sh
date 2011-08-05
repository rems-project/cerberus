#!/bin/bash

MENHIR_ARGS=""
DEBUG="yes"

if [[ "$DEBUG" -eq "yes" ]]
then
  MENHIR_ARGS="--comment" # --trace"
fi

echo $MENHIR_ARGS

BATTERIES=`ocamlfind query batteries`

ln -s $BATTERIES/batSet.cmi _build/lib/frontc/
ln -s $BATTERIES/batBig_int.cmi _build/lib/frontc/
ln -s $BATTERIES/batteries.cmi _build/lib/frontc/

mv lib/frontc/cparser.mly~ lib/frontc/cparser.mly
menhir $MENHIR_ARGS --ocamlc 'ocamlfind ocamlc -I _build/lib/frontc -I _build/src -rectypes' --infer lib/frontc/cparser.mly
mv lib/frontc/cparser.mly lib/frontc/cparser.mly~
