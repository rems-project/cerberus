#!/bin/bash

SUCCESS=$(git ls-files success/*.c | wc -l)
FAILURE=$(git ls-files fail | grep -E '.c$' | wc -l)
UNSUPP=$(git ls-files not_supported | grep -E '.c' | wc -l)
INVALID=$(git ls-files invalid/*.c | wc -l)
UNDEFINED=$(git ls-files undefined/*.c | wc -l)

VALID_TOTAL=$((SUCCESS+FAILURE))
TOTAL=$((VALID_TOTAL+UNSUPP+UNDEFINED+INVALID))

SUCCRATE=$(((SUCCESS*1000)/VALID_TOTAL))

echo Total of tests: $TOTAL
echo Success: $SUCCESS
echo Failure: $FAILURE
echo Unsupported: $UNSUPP
echo Undefined: $UNDEFINED
echo Invalid: $INVALID
echo ""
echo Total of valid tests: $VALID_TOTAL
echo Success percentage: ${SUCCRATE:0:2}.${SUCCRATE:2:1}%
echo ""
echo Failure by type:
cd fail
for d in `find . -type d ! -path .`
do
	echo $d: $(git ls-files $d/*.c | wc -l)
done
cd ..
echo ""
echo Unsupported by type:
cd not_supported
for d in `find . -type d ! -path .`
do
	echo $d: $(git ls-files $d/*.c | wc -l)
done

