#!/bin/bash

trap 'repair_dune' SIGINT

# GNU vs BSD
# function sedi(){
# if sed --version 2>/dev/null 1>/dev/null; then
#   echo "sed -i -e '$1' $2"
# else
#   echo "sed -i '' -e '$1' $2"
# fi
# }

function repair_dune() {
  case "$(uname -s)" in
  Darwin)
    sed -i '' -e '/(dirs/s/ coq//' dune
    ;;
  *)
    sed -i -e '/(dirs/s/ coq//' dune
    ;;
  esac
}

function add_coq() {
    case "$(uname -s)" in
  Darwin)
    sed -i '' -e 's/(dirs \([^)]*\))/(dirs \1 coq)/' dune
    ;;
  *)
    sed -i -e 's/(dirs \([^)]*\))/(dirs \1 coq)/' dune
    ;;
  esac
}

add_coq
eval $1
repair_dune
