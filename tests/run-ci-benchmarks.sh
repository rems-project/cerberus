#!/bin/bash

JSON_FILE="benchmark-data.json"

cat << EOF >> ${JSON_FILE}
[
EOF

DIRNAME=$(dirname "$0")

SUCC=$(find "${DIRNAME}"/cn -name '*.c' | grep -v '\.error\.c')

COUNT=0
for TEST in ${SUCC}; do
  let COUNT=${COUNT}+1
done

INDEX=0
echo $SUCC
echo $COUNT
for TEST in ${SUCC}; do
  echo ${INDEX}

  # Record wall clock time in seconds
  /usr/bin/time -f "%e" -o /tmp/time cn verify ${TEST}
  TIME=$(cat /tmp/time)

  # If we're last, don't print a trailing comma.
  if [[ ${INDEX} -eq ${COUNT}-1 ]]; then
    # Hack to output JSON.
    cat << EOF >> ${JSON_FILE}
    {
	"name": "${TEST}",
        "unit": "Seconds",
	"value": ${TIME}
    }
EOF
  else
    cat << EOF >> ${JSON_FILE}
    {
	"name": "${TEST}",
        "unit": "Seconds",
	"value": ${TIME}
    },
EOF
  fi

  let INDEX=${INDEX}+1
done

cat << EOF >> ${JSON_FILE}
]
EOF

cat ${JSON_FILE}
