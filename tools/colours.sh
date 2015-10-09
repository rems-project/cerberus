#!/bin/sh

if [ "$1" = "lem" ]; then
  cat - | sed -E -e "s,^  Warning.*,$(tput setaf 3)&$(tput sgr 0)," -e "s,^  (Error|Type error).*,$(tput setaf 1)&$(tput sgr 0),"
else
  cat - | sed -E -e "s,^Warning.*,$(tput setaf 3)&$(tput sgr 0)," -e "s,^Error.*,$(tput setaf 1)&$(tput sgr 0),"
fi
