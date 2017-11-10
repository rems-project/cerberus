// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_447.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x5D6C05BAL;
static uint16_t g_5 = 0x74DDL;
static int64_t g_10 = (-1L);
static int64_t g_11 = 0xCD49598AAF0A9B27LL;
static uint32_t g_12 = 9UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_7 = 0xD6B65720L;
    int32_t l_8 = (-7L);
    int32_t l_9 = 0x10EC3203L;
    for (g_2 = 0; (g_2 <= (-18)); g_2--)
    { 
        g_5 = 0L;
    }
    g_2 = g_2;
    if (g_5)
    { 
        int32_t l_6 = (-2L);
        l_6 ^= g_5;
        g_2 = g_2;
        l_6 = g_5;
        g_2 |= l_7;
    }
    else
    { 
        return g_5;
    }
    g_12++;
    return l_8;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
