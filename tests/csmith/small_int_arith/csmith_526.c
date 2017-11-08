// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_526.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static uint16_t g_6 = 0UL;
static uint16_t g_13 = 65527UL;
static int8_t g_21 = 0x67L;
static uint16_t g_30 = 65535UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    const int32_t l_5 = 0L;
    int8_t l_9 = (-1L);
    const uint32_t l_15 = 4294967295UL;
    uint64_t l_16 = 0x12530A9BCA7B5CF1LL;
    int32_t l_17 = 0x17F4039EL;
    uint32_t l_18 = 0x6B42BE19L;
    int32_t l_19 = (-4L);
    int32_t l_20 = 1L;
    int32_t l_22 = 0x3BA6AED1L;
    int32_t l_23 = (-1L);
    int32_t l_24 = 0x6EF3B063L;
    int32_t l_25 = (-1L);
    int32_t l_26 = 1L;
    int32_t l_27 = (-1L);
    int32_t l_28 = (-1L);
    int32_t l_29 = 0xC5674FA7L;
    int16_t l_33 = 1L;
    for (g_2 = (-13); (g_2 < (-1)); ++g_2)
    { 
        uint16_t l_7 = 65535UL;
        int32_t l_8 = 0x307D7C11L;
        g_6 = l_5;
        l_7 = g_6;
        l_8 = 0xF7FBF212L;
        if (g_6)
            break;
    }
    if (l_9)
    { 
        uint8_t l_10 = 5UL;
        l_10++;
        if (g_2)
            goto lbl_14;
        g_2 = l_5;
        g_2 = g_2;
    }
    else
    { 
lbl_14:
        g_13 = g_6;
        l_16 = l_15;
        l_18 ^= l_17;
    }
    g_30++;
    l_33 = g_21;
    return l_17;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
