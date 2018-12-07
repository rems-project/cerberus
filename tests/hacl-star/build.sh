#!/bin/sh
#gcc -fPIC -Wall -Wextra -Wno-parentheses -Wno-unused compact/*.c minimal/*.c -I. -Iinclude -Icompact -Iminimal -shared -olibhacl.so -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all

echo "Testing Hacl_Hash.c"
cerberus compact/Hacl_Hash.c -I include -I minimal --exec --batch # it works faster without --sequentialise --rewrite

