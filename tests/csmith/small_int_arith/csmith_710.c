// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_710.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static int16_t g_4 = 0xE00FL;
static int32_t g_5 = 1L;
static int32_t g_10 = 9L;
static int32_t g_19 = 0xEBD004DDL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint8_t l_6 = 0x18L;
    int32_t l_7 = 5L;
    int32_t l_11 = (-1L);
    int32_t l_12 = (-1L);
    int8_t l_13 = (-3L);
    int8_t l_14 = 0L;
    int32_t l_15 = 7L;
    int32_t l_16 = 6L;
    int32_t l_17 = 0xC1DE6FC6L;
    int32_t l_18 = 1L;
    int32_t l_20 = (-1L);
    int32_t l_21 = (-5L);
    uint8_t l_22 = 0x66L;
lbl_9:
    if (g_2)
    { 
        int16_t l_3 = 0x5286L;
        l_3 = (-7L);
        g_4 = g_2;
        g_5 = 0x1C0F8067L;
        l_7 ^= l_6;
        if (g_2)
            goto lbl_9;
    }
    else
    { 
        uint32_t l_8 = 4UL;
        l_8 = 0xCF95751CL;
    }
    g_10 = l_7;
    l_22--;
    g_19 = 0xD9796A0BL;
    return g_10;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
