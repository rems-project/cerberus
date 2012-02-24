#!/bin/bash
export OCAMLRUNPARAM=b

for FILE in "$@"
do
  echo "${FILE}:"
  cat -n "${FILE}" && ./chickenpox.byte "${FILE}"
done
