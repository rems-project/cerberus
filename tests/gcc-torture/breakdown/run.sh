#!/bin/bash

SUCCESS=$(ls success/*.c | wc -l)
LIMBUS=$(ls limbus/*.c | wc -l)
FAILURE=$(ls -R fail | grep -E '\.c' | wc -l)
NOTSTD=$(ls -R not_std_compliant | grep -E '\.c' | wc -l)
UNSUPP=$(ls -R not_supported | grep -E '\.c' | wc -l)
INVALID=$(ls invalid/*.c | wc -l)
UNDEFINED=$(ls undefined/*.c | wc -l)

VALID_TOTAL=$((SUCCESS+LIMBUS+FAILURE))
TOTAL=$((VALID_TOTAL+UNSUPP+UNDEFINED+INVALID))

SUCCRATE=$((((SUCCESS+LIMBUS)*1000)/VALID_TOTAL))

echo Total of tests: $TOTAL
echo Success: $((SUCCESS+LIMBUS))
echo Limbus \(stack overflow otherwise\): $LIMBUS
echo Not STD compliant: $NOTSTD
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
	echo $d: $(ls $d/*.c | wc -l)
done
cd ..
echo ""
echo Unsupported by type:
cd not_supported
for d in `find . -type d ! -path .`
do
	echo $d: $(ls $d/*.c | wc -l)
done
cd ..
echo ""
echo Not STD compliant by type:
cd not_std_compliant
for d in `find . -type d ! -path .`
do
	echo $d: $(ls $d/*.c | wc -l)
done

