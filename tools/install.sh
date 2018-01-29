#!/bin/sh

PREFIX=$1

# If empty prefix
! [ $1 ] && echo Please specify prefix location! && exit 1

#WARN: cerberus should be in $PREFIX/bitbucket/csem
! [ $PREFIX/bitbucket/csem ] && echo Please specify prefix such that \$PREFIX/bitbucket/csem && exit 1

# If opam exists quit
[ `which opam` ] && echo Opam already installed! && exit 1

# Get OPAM
wget https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s $PREFIX/usr/local/bin

opam init --comp 4.06.0
eval `opam config env`

# Install Ocamlfind Zarith and Num
opam install ocamlfind zarith num

# Install lem
cd $PREFIX/bitbucket/
git clone git@bitbucket.org:Peter_Sewell/lem.git
cd lem
make
cd ocaml-lib && make install

# Update PATH
echo export PATH=${PREFIX}/bitbucket/lem:\$PATH >> ~/.profile
export PATH=${PREFIX}/bitbucket/lem:$PATH

# Install cmdliner menhir pprint Z3
opam install cmdliner menhir pprint z3

# Update LD_LIBRARY_PATH
echo export LD_LIBRARY_PATH=\$LD_LIBRARY_PATH:`ocamlfind query z3` >> ~./profile
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`ocamlfind query z3`

# Update PATH
echo export PATH=${PREFIX}/bitbucket/csem:\$PATH >> ~/.profile
export PATH=${PREFIX}/bitbucket/csem:$PATH
echo export CERB_PATH=${PREFIX}/bitbucket/csem >> ~/.profile
export CERB_PATH=${PREFIX}/bitbucket/csem

# Update cerberus
cd $PREFIX/bitbucket/csem
hg pull
make
