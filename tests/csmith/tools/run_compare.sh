#!/bin/sh

gtimeout 10s clang -DCSMITH_MINIMAL -I ../runtime -w -o compare.out $@ && ./compare.out
gtimeout 30s cerberus --cpp="cc -E -nostdinc -undef -D__cerb__ -I $CERB_PATH/include/c/libc -I $CERB_PATH/include/c/posix -DCSMITH_MINIMAL -I ../runtime" --exec --batch $@
rm compare.out