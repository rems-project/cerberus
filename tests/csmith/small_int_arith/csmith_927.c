// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_927.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-1L);
static uint64_t g_3 = 0x2F4A8B108F8256A9LL;
static int32_t g_4 = 0xDE2BBEF7L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
lbl_7:
    if (g_2)
    { 
        g_3 = g_2;
        g_4 = 0xEA6801FCL;
    }
    else
    { 
        int64_t l_5 = 0x4B4B13281D21F1EBLL;
        int32_t l_6 = 0L;
        l_5 = g_4;
        l_6 = g_2;
        if (g_2)
            goto lbl_7;
    }
    g_4 &= 1L;
    return g_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
