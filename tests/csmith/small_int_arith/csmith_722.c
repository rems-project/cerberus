// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_722.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-1L);
static uint64_t g_9 = 1UL;
static int16_t g_12 = 0x13A6L;
static int64_t g_13 = 0xCFBCE008FB0B44CFLL;
static uint8_t g_15 = 246UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int8_t l_5 = 0x8AL;
    int32_t l_6 = 0L;
    int32_t l_11 = 0xA7525D2DL;
    int32_t l_14 = (-1L);
    for (g_2 = 0; (g_2 == (-10)); --g_2)
    { 
        int32_t l_7 = 0xE3E63E31L;
        int32_t l_8 = 0x22A149CEL;
        l_5 = g_2;
        l_6 = (-3L);
        l_8 &= l_7;
    }
    l_6 = l_5;
    if (g_2)
    { 
        l_6 = g_2;
        if (g_2)
            goto lbl_10;
    }
    else
    { 
lbl_10:
        g_9 |= g_2;
        ++g_15;
    }
    return g_13;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
