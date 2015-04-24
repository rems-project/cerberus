#!/bin/bash

file=smith*.c

rm -f CERB_STATUS
for i in $file; do
  cerberus --progress $i &> /dev/null;
  case $? in
    10)
          echo "$i    PARS" >> CERB_STATUS
          ;;
    11)
          echo "$i    DESU" >> CERB_STATUS
          ;;
    12)
          echo "$i    TYPE" >> CERB_STATUS
          ;;
    13)
          echo "$i    ELAB" >> CERB_STATUS
          ;;
    14)
          echo "$i    EXEC" >> CERB_STATUS
          ;;
    *)
          echo "$i    FAIL" >> CERB_STATUS
          ;;
  esac;
  echo "DONE with $i"
done

n=`wc -l CERB_STATUS | awk '{print $1}'`
failed=`grep FAIL CERB_STATUS | wc -l | awk '{print $1}'`

executed=`grep EXEC CERB_STATUS | wc -l | awk '{print $1}'`
elaborated=$(expr `grep ELAB CERB_STATUS | wc -l | awk '{print $1}'` + $executed)
typed=$(expr `grep TYPE CERB_STATUS | wc -l | awk '{print $1}'` + $elaborated)
desugared=$(expr `grep DESUG CERB_STATUS | wc -l | awk '{print $1}'` + $typed)
parsed=$(expr `grep PARS CERB_STATUS | wc -l | awk '{print $1}'` + $desugared)
echo "[found $n test(s)]"
echo "parsed:     $parsed (`bc <<< "scaled=2; 100 * $parsed / $n"`%)"
echo "desugared:  $desugared (`bc <<< "scaled=2; 100 * $desugared / $n"`%)"
echo "typed:      $typed (`bc <<< "scaled=2; 100 * $typed / $n"`%)"
echo "elaborated: $elaborated (`bc <<< "scaled=2; 100 * $elaborated / $n"`%)"
echo "executed:   $executed (`bc <<< "scaled=2; 100 * $executed / $n"`%)"
echo "----------------------------------"
echo "failed:     $failed (`bc <<< "scaled=2; 100 * $failed / $n"`%)"
