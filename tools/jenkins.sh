#!/bin/bash

export CERB_PATH=/local/jenkins/home/workspace/rems/cerberus
export DEPPATH=$CERB_PATH/dependencies
export LEMPATH=$DEPPATH/lem
export OPAMROOT=$DEPPATH/.opam
export BINPATH=$DEPPATH/bin
export PATH=$LEMPATH:$BINPATH:$PATH
export LEMLIB=$LEMPATH/library

if ! hash opam 2> /dev/null; then
  echo "Installing OPAM!"
  mkdir -p $BINPATH
  wget https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s $BINPATH 4.06.0
  eval `opam config env`
  opam init
  opam install ocamlfind cmdliner menhir pprint zarith yojson
  opam install ppx_deriving ppx_sexp_conv sexplib sha
  opam install z3
fi


if ! hash lem 2> /dev/null; then
  echo "Install LEM"
  cd $DEPPATH
  git clone https://github.com/rems-project/lem
  cd lem
  make
  cd ocaml-lib
  make install
  cd $CERB_PATH
fi

# Initialise OPAM
. $OPAMROOT/opam-init/init.sh > /dev/null 2> /dev/null || true

# Clean and make Cerberus
make clear
make

# Run tests
cd tests
./run.sh
