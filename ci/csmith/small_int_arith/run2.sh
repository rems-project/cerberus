for file in csmith_???.c; do
    rm -f a.out; gcc-5 -DCSMITH_MINIMAL -I /Users/catzilla/Applications/Sources/csmith-2.2.0/runtime $file 2> /dev/null; gtimeout 30s ./a.out > gcc.out;
    ret=$?;
    echo $ret >> gcc.out;
    if [ $ret == 124 ]; then
        # the program doesn't seem to terminate
        echo "XX $file";
        continue
    fi;
    
    gtimeout 30s cerberus --exec $file 2>&1 > cerb.out;
    ret=$?
    echo $ret >> cerb.out
    if [ $ret == 124 ]; then
        # the cerberus doesn't seem to terminate
        echo "TO $file";
        continue
    fi;
    
    if diff -q gcc.out cerb.out > /dev/null ; then
        echo "OK $file"
    else
        echo "KO $file"
    fi;
done;

rm -f cerb.out gcc.out
