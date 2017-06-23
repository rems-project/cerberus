function testWithCerberus {
  for f in *.c
  do
    cerberus $f 2>&1 > /dev/null | grep -R $1
    if [ $? -eq 0 ]; then
      echo Move test $f
      mv $f $2
    fi
  done
}

# Go to gcc-torture/execute folder
cd execute

## Delete folders that we don't support
rm -rf ieee
rm -rf builtins

echo 1. Save tests

ls -R | grep ".\>" | sort -u > ../all-tests

## Save unsupported test names
rm -rf ../unsupported
touch ../unsupported

echo 2. Identify unsupported tests
function unsupp {
  echo - $1
  grep -R $1 . | awk -F ":" '{print $1;}' | cut -c3- | uniq >> ../unsupported
}

unsupp _Complex
unsupp float
unsupp double
unsupp asm
unsupp va_start
unsupp alloca
unsupp __FUNCTION__
unsupp __func__
unsupp wchar # wchar_t literals are not supported

#some builtins are supporeted (see cerberus.h)
unsupp __builtin_ffs
unsupp __builtin_constant_p
unsupp __builtin_return_address
unsupp __builtin_ctz
unsupp __builtin_bswap
unsupp __builtin_longjmp
unsupp __builtin_mul_overflow

## Catch GNU extensions and implicit function declarations
function callClang {
  echo - $1
  cat ../all-tests | xargs -I '{}' clang --pedantic -std=c11 '{}' 2>&1 > /dev/null \
    | grep $1 | awk -F ":" '{print $1;}' >> ../unsupported
}

callClang GNU
callClang implicit-function-declaration
rm a.out

## Sort uniq unsupported
sort -u ../unsupported -o ../unsupported

## Remaining tests
comm -23 ../all-tests ../unsupported > ../remaining

echo 3. Copying tests

# Copying tests
mkdir ../sorted/
mkdir ../sorted/unsupported
mkdir ../sorted/remaining
mkdir ../sorted/execute

cat ../unsupported | xargs -I '{}' cp '{}' ../sorted/unsupported
cat ../remaining | xargs -I '{}' cp '{}' ../sorted/remaining

rm ../all-tests ../remaining ../unsupported

cd ../sorted/remaining

echo 4. Testing remaining tests with Cerberus
for f in *.c
do
  cerberus $f 2>&1 > /dev/null
  if [ $? -eq 0 ]; then
    echo Move test $f
    mv $f ../execute
  fi
done

echo 5. Add Cerberus header to every file
cp ../../cerberus.h .
gsed -i '1i\#include "cerberus.h"' *.c
rm *.temp

echo 6. Copy anything working...
for f in *.c
do
  cerberus $f 2>&1 > /dev/null
  if [ $? -eq 0 ]; then
    echo Move test $f
    mv $f ../execute
  fi
done

## Bitfield are not supported
testWithCerberus SDecl_bitfield ../unsupported

echo 7. Parsing issues
mkdir ../parsing
testWithCerberus End_of_file ../parsing
testWithCerberus token ../parsing

echo 8. Separate by Cerberus error messages
mkdir ../issues

mkdir ../issues/switch
grep -R switch . | awk -F ":" '{print $1;}' | uniq | xargs -I '{}' mv '{}' ../issues/switch
#testWithCerberus AilSswitch ../issues/switch

mkdir ../issues/compound
testWithCerberus AilEcompound ../issues/compound

mkdir ../issues/memberofptr
testWithCerberus AilEmemberofptr ../issues/memberofptr

mkdir ../issues/builtin
testWithCerberus AilEbuiltin ../issues/builtin

mkdir ../issues/integer_range
testWithCerberus integer_range ../issues/integer_range

## If nonderterminism issue, try to execute
echo 9. Nondeterminism issue...
for f in *.c
do
  cerberus $f 2>&1 > /dev/null | grep -R Nondeterminism
  if [ $? -eq 0 ]; then
    cerberus $f --exec > /dev/null
    if [ $? -eq 0 ]; then
      echo Move test $f
      mv $f ../execute
    fi
  fi
done

for f in *.c
do
  cerberus $f 2>&1 > /dev/null | grep Nondeterminism
  if [ $? -eq 0 ]; then
    cerberus $f --exec 2>&1 > /dev/null | grep AilEmemberofptr
    if [ $? -eq 0 ]; then
      echo Move test $f
      mv $f ../issues/memberofptr
    fi
  fi
done

echo 6. Using CIL to transform files

cd ../parsing

gsed -i -e "1d" *.c
gsed -i '/include/d' *.c

mkdir cil
for f in *.c
do
  ../../transform.native $f cil/$f 2>&1 > /dev/null | grep -R Error
  if [ $? -eq 1 ]; then
    rm $f
  fi
done
rm *.temp

mkdir ../cil

cd cil

cp ../../../cerberus.h .
gsed -i '1i\#include "cerberus.h"' *.c

for f in *.c
do
  cerberus $f 2>&1 > /dev/null
  if [ $? -eq 0 ]; then
    echo Move test $f
    mv $f ../../cil
    rm ../$f
  fi
done
