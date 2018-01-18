// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_624.c
#include "csmith.h"


static long __undefined;



static uint16_t g_3 = 0x4DD0L;
static uint32_t g_5 = 0xF0AA6E6FL;
static int64_t g_12 = (-1L);
static uint32_t g_14 = 0xC14AB653L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int32_t l_2 = 0xF43B7C7CL;
    int32_t l_7 = 0xD210EC32L;
    int8_t l_8 = 0x8AL;
    uint16_t l_13 = 0x6B42L;
    l_2 = (-1L);
    if (g_3)
    { 
        const int32_t l_4 = 1L;
        int32_t l_6 = 0x188E17B8L;
        g_5 |= l_4;
        l_6 = l_4;
        l_6 = 0x320E32CFL;
        l_6 ^= 0xED6B6572L;
    }
    else
    { 
        l_7 = 4L;
        l_7 = g_3;
        return l_8;
    }
    for (g_3 = 0; (g_3 <= 11); g_3++)
    { 
        uint32_t l_11 = 0x912530A9L;
        l_11 = g_5;
        g_12 |= g_5;
    }
    g_14 = l_13;
    return g_5;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
