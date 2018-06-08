#!/bin/bash

rm -rf tmp
mkdir -p tmp
cp execute/*c tmp/
cp cerberus.h tmp

cd tmp

grep -Rl complex . | xargs rm
grep -Rl __Complex . | xargs rm
grep -Rl asm . | xargs rm
grep -Rl va_start . | xargs rm
grep -Rl alloca . | xargs rm
grep -Rl __FUNCTION__ . | xargs rm
grep -Rl __func__ . | xargs rm
grep -Rl wchar . | xargs rm

grep -Rl __builtin_ffs . | xargs rm
grep -Rl __builtin_constant_p . | xargs rm
grep -Rl __builtin_return_address . | xargs rm
grep -Rl __builtin_ctz . | xargs rm
grep -Rl __builtin_bswap . | xargs rm
grep -Rl __builtin_longjmp . | xargs rm
grep -Rl __builtin_mul_overflow . | xargs rm

touch success
touch failure
touch log

success=0
failure=0

for f in *.c
do
  echo Testing $f >> log
  # Change to AINSI style
  cproto -a -q -E 0 $f 2>/dev/null
  # Remove any includes
  sed -i '' '/include/d' $f
  # Add cerberus.h
  sed -i '' '1i\
  #include "cerberus.h"
  ' $f
  # Run cerberus
  result=$(cerberus --rewrite --exec --batch $f 2>&1)
  echo $result >> log
  echo $result | grep EXIT
  if [ $? -eq 0 ]; then
    echo SUCCESS
    echo SUCCESS >> $result
    ((success++))
  else
    echo $result | grep "Specified(0)"
    if [ $? -eq 0 ]; then
      echo SUCCESS
      echo SUCCESS >> $result
      ((success++))
      echo $f >> success
    else
      echo FAIL
      echo FAIL >> $result
      ((failure++))
      echo $f >> failure
    fi
  fi
done

echo SUCCESS: $success
echo FAILURE: $failure

cd ..

mv tmp/success .
mv tmp/failure .
mv tmp/log .