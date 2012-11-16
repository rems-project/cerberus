#!/bin/bash

PATH=~/wg14
CUR=`/usr/bin/ls -1v $PATH/new/ | /usr/bin/tail -n 1`

STATUS=0

while [ "$STATUS" == "0" ]
do
CUR=$(($CUR + 1))
/usr/bin/wget http://www.open-std.org/jtc1/sc22/wg14/$CUR
STATUS=$?
done
