// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_458.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0xC70BB743L;
static uint32_t g_3 = 4294967290UL;
static int32_t g_6 = 0xB80BE39EL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    const uint32_t l_4 = 8UL;
    int32_t l_5 = (-1L);
    uint32_t l_10 = 0x73E7ED6FL;
    if (g_2)
    { 
        g_3 = 0x6E871D97L;
        l_5 = l_4;
    }
    else
    { 
        uint32_t l_7 = 6UL;
        l_7++;
        return l_10;
    }
    for (g_2 = 0; (g_2 == 14); g_2++)
    { 
        int64_t l_13 = (-1L);
        g_6 |= 0xCF5A8B06L;
        l_13 |= g_3;
        g_6 = g_2;
    }
    g_6 = g_3;
    g_6 = g_3;
    return l_5;
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
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
