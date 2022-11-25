#!/bin/sh
if [ "$(basename "$1")" = "CRelationClasses.mli" ]; then
    patch -p0 -r 0 -s --follow-symlinks -o - $1 -i coq/extracted/CRelationClasses.mli.patch
else
    cat $1
fi

