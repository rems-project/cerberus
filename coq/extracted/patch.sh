#!/bin/sh

if patch --version | grep 'GNU' --silent; then
GNU_ARGS="--read-only=ignore --follow-symlinks"
fi
patch -p0 -r 0 -s $GNU_ARGS -o - $1 -i extracted/CRelationClasses.mli.patch
