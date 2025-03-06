#!/bin/bash

# Sets the CERB and CERB_INSTALL_PREFIX variables for a given backend
# (given in $1).
function set_cerberus_exec() {
  # Use the provided path to cerberus, otherwise defaults the local version
  # built by dune
  CERB="${WITH_CERB:=dune exec --no-print-directory $1 --no-build --}"
  if [[ ! -z "${USE_OPAM+x}" ]]; then
    echo -e "\x1b[33;1mUsing opam installed $1\x1b[0m";
    CERB=$OPAM_SWITCH_PREFIX/bin/$1
    export CERB_INSTALL_PREFIX=$OPAM_SWITCH_PREFIX
  else
    # Otherwise, Cerb_runtime will find the runtime in _build/
    unset CERB_INSTALL_PREFIX
  fi
}
