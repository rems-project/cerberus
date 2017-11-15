#!/bin/bash

#DIR=/home/jm/work/wg14
DIR=/home/pes20/tmp/wg14
#CUR=$(/usr/bin/ls -1v "$DIR"/new/ | /usr/bin/tail -n 1)
CUR=$(/bin/ls -1v "$DIR"/new/ | /usr/bin/tail -n 1)


# missing
# 4209
# 6178
# 6179
# 6391
# 6452
# 6453
# 6538
# 7018
# 7019
# 7020
# 7021 
# 7156
# 7157
# 7158 
# 7159 
# 7161
# 7162
# 7163 
# 7164 
# 7741 
# 9316 
if [[ -z "$CUR" ]]; then
  CUR=14103

fi

STATUS=0

while [ "$STATUS" == "0" ]
do
  CUR=$(($CUR + 1))
  curl -sf http://www.open-std.org/jtc1/sc22/wg14/$CUR -o "$DIR"/new/$CUR
  STATUS=$?
done
