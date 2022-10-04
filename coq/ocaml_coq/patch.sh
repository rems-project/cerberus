#!/bin/sh
if [ "$(basename "$1")" = "CRelationClasses.mli" ]; then
    patch -p0 -r 0 -s --follow-symlinks -o - $1 -i coq/ocaml_coq/CRelationClasses.mli.patch
else
    cat $1
fi

