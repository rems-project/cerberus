#!/bin/bash

JSON_FILE="benchmark-data.json"

cat << EOF >> ${JSON_FILE}
[
EOF

DIRNAME=$(dirname "$0")

SUCC=$(find "${DIRNAME}"/cn -name '*.c' | grep -v '\.error\.c')

for TEST in ${SUCC}; do
  # Record wall clock time in seconds
  /usr/bin/time -f "%e" -o /tmp/time cn verify ${TEST}
  TIME=$(cat /tmp/time)

  # Hack to output JSON.
  cat << EOF >> ${JSON_FILE}
    {
	"name": "${TEST}",
        "unit": "Seconds",
	"value": ${TIME}
    },
EOF
done

cat << EOF >> ${JSON_FILE}
]
EOF

cat ${JSON_FILE}
