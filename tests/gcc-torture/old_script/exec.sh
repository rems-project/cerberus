if [ ! -d "sorted/execute" ]; then
  echo Directory sorted/execute does not exist.
  exit 1
fi

rm -rf passed failed
touch passed
touch failed

cp cerberus.h sorted/execute/
cd sorted/execute

gsed -i '/include/d' *.c
gsed -i '/void abort/d' *.c
gsed -i '/void exit/d' *.c
gsed -i '1i\#include "cerberus.h"' *.c

touch failed_temp
for f in *.c
do
  echo Test $f
  cerberus --exec --batch $f | grep 'Defined {value: "Specified(0)", stdout:' > /dev/null
  if [ $? -eq 0 ]; then
    echo $f >> ../../passed
  else
    echo "FAILED"
    echo $f >> failed_temp
  fi
done

while read f; do
  echo Test $f
  cerberus --exec --batch $f | grep 'Undefined' > /dev/null
  if [ $? -eq 0 ]; then
    echo $f >> ../../passed
  else
    echo "FAILED"
    echo $f >> ../../failed
  fi
done < failed_temp

rm -rf failed_temp

echo `cat ../../passed | wc -l` tests passed
echo `cat ../../failed | wc -l` tests failed