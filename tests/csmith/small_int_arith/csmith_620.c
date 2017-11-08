// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_620.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-1L);
static uint32_t g_3 = 1UL;
static uint64_t g_6 = 18446744073709551611UL;
static uint64_t g_10 = 8UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint32_t l_5 = 4294967295UL;
    int32_t l_7 = 0x9B7928FBL;
    if (g_2)
    { 
        int8_t l_4 = (-1L);
        g_3 = g_2;
        l_4 = g_2;
    }
    else
    { 
        g_6 = l_5;
    }
    l_7 |= g_6;
    if (l_7)
    { 
        int32_t l_8 = 6L;
        l_8 ^= (-6L);
    }
    else
    { 
        int64_t l_9 = 0x7979B3895196EE4ELL;
        int32_t l_11 = 0x468A07C6L;
        l_9 = l_5;
        l_7 ^= l_9;
        g_10 |= l_9;
        l_11 ^= l_5;
    }
    return g_6;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
