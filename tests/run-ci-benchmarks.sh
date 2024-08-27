#!/usr/bin/env bash
set -euo pipefail -o noclobber
# set -xv # uncomment to debug variables

JSON_FILE="benchmark-data.json"

echo "[" >> "${JSON_FILE}"

DIRNAME=$(dirname "$0")

TESTS=$(find "${DIRNAME}"/cn -name '*.c')

COUNT=0
for TEST in ${TESTS}; do
  let COUNT=${COUNT}+1
done

INDEX=0
for TEST in ${TESTS}; do

  # Record wall clock time in seconds
  /usr/bin/time -f "%e" -o /tmp/time cn verify "${TEST}" || true
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

echo "]" >> "${JSON_FILE}"

jq . "${JSON_FILE}"
