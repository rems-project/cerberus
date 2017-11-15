// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_483.c
#include "csmith.h"


static long __undefined;



static uint64_t g_5 = 0xA77C8748AFA2FAFDLL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int64_t l_2 = 9L;
    int32_t l_3 = 4L;
    uint16_t l_4 = 0xFAB8L;
    uint32_t l_8 = 0UL;
    l_3 |= l_2;
    l_3 &= (-1L);
    if (l_4)
    { 
        int8_t l_6 = 0xEEL;
        l_6 = g_5;
    }
    else
    { 
        uint16_t l_7 = 0UL;
        uint8_t l_9 = 1UL;
        l_8 = l_7;
        l_3 = 0x780CA9F8L;
        l_9 = g_5;
    }
    return l_3;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
