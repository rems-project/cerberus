#!/bin/sh
#gcc -fPIC -Wall -Wextra -Wno-parentheses -Wno-unused compact/*.c minimal/*.c -I. -Iinclude -Icompact -Iminimal -shared -olibhacl.so -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all

echo "Testing Hash"
cerberus compact/Hacl_Hash.c -I include -I minimal --exec --batch # it works faster without --sequentialise --rewrite

echo "Testing Chacha2"
cerberus compact/Hacl_Chacha20.c -I include -I minimal --exec --batch

echo "Testing Poly1305"
cerberus compact/Hacl_Poly1305_64.c -I include -I minimal --exec --batch

# It takes too long to execute!
#echo "Testing Curve25519"
#cerberus compact/Hacl_Curve25519.c -I include -I minimal --exec --batch --rewrite --sequentialise

