#!/bin/sh

if [[ "$OSTYPE" == "linux-gnu" ]]; then
  $@
else
  if [ "$1" = "lem" ]; then
    ($@) 2>&1 | sed -E -e "s,^  Warning.*,$(tput setaf 3)&$(tput sgr 0)," -e "s,^  (Error|Type error).*,$(tput setaf 1)&$(tput sgr 0),";
    exit ${PIPESTATUS[0]}
  else
    ($@) | sed -E -e "s,^Warning.*,$(tput setaf 3)&$(tput sgr 0)," -e "s,^Error.*,$(tput setaf 1)&$(tput sgr 0),";
    exit ${PIPESTATUS[0]}
  fi
fi
