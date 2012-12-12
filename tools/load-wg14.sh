#!/bin/bash

DIR=/home/jm/work/wg14
CUR=$(/usr/bin/ls -1v "$DIR"/new/ | /usr/bin/tail -n 1)

if [[ -z "$CUR" ]]; then
  CUR=0
fi

STATUS=0

while [ "$STATUS" == "0" ]
do
  CUR=$(($CUR + 1))
  curl -sf http://www.open-std.org/jtc1/sc22/wg14/$CUR -o "$DIR"/new/$CUR
  STATUS=$?
done
