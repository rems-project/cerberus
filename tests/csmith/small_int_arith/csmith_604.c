// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_604.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 6L;
static int64_t g_12 = 0L;
static int16_t g_14 = 0x6F9BL;
static uint32_t g_15 = 0xD816F93BL;
static int64_t g_23 = (-9L);
static int16_t g_24 = 3L;
static uint16_t g_25 = 8UL;
static int16_t g_28 = 1L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_3 = 0UL;
    int32_t l_4 = 0x822B1658L;
    int64_t l_5 = 0xB5CABFC3938DD44ALL;
    int64_t l_22 = 0x07C1ABDF11CAF1E2LL;
    if (g_2)
    { 
        uint16_t l_6 = 5UL;
        l_4 = l_3;
        g_2 = l_4;
        l_5 |= g_2;
        ++l_6;
    }
    else
    { 
        int32_t l_9 = 0x2F67D50FL;
        int32_t l_10 = 4L;
        int32_t l_11 = 0xA8FECF79L;
        int32_t l_13 = 0x89051546L;
        g_2 = g_2;
        --g_15;
        l_4 = l_4;
        l_9 = l_11;
    }
    l_4 = 0x76270E7AL;
    if (l_5)
    { 
        uint32_t l_18 = 0x22D5FBA2L;
        g_2 = g_14;
        if (g_2)
            goto lbl_19;
lbl_19:
        l_4 = l_18;
        g_2 = g_2;
    }
    else
    { 
        g_2 &= g_12;
        g_2 = l_5;
    }
    if (l_5)
    { 
        uint64_t l_20 = 18446744073709551615UL;
        int32_t l_21 = (-4L);
        l_20 ^= g_15;
        ++g_25;
        l_21 = 0x67F5D1CCL;
    }
    else
    { 
        uint64_t l_29 = 0x7DCC3592E7BAA9D7LL;
        ++l_29;
        g_2 = l_29;
    }
    return l_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
