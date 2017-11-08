// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_508.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 4294967295UL;
static uint16_t g_4 = 0UL;
static int32_t g_6 = 8L;
static int64_t g_8 = 0x0A50B5F0B101AAE4LL;
static int16_t g_10 = 0xF8B8L;
static uint64_t g_12 = 0x5F9C7104272BA75ALL;
static int16_t g_15 = 0xC0E2L;
static uint32_t g_20 = 1UL;
static int8_t g_23 = 0L;
static uint8_t g_25 = 0x3AL;
static uint32_t g_30 = 6UL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int64_t l_2 = 0x4A12B57E8B72FD49LL;
    int64_t l_7 = 1L;
    int32_t l_9 = (-7L);
    int32_t l_17 = 0x678E045DL;
    int32_t l_18 = (-2L);
lbl_28:
    if (l_2)
    { 
        uint32_t l_5 = 1UL;
        g_4 = g_3;
        g_6 = l_5;
        if (g_3)
            goto lbl_16;
    }
    else
    { 
        int8_t l_11 = 0xB8L;
        g_12--;
    }
    if (g_10)
    { 
lbl_16:
        g_15 = g_12;
lbl_24:
        l_17 = g_12;
        return l_18;
    }
    else
    { 
        int8_t l_19 = 5L;
        l_9 &= g_15;
        g_20--;
    }
    g_23 = g_15;
    if (g_10)
    { 
        if (g_12)
            goto lbl_24;
lbl_29:
        g_25--;
        if (g_15)
            goto lbl_28;
        if (g_25)
            goto lbl_29;
    }
    else
    { 
        l_18 &= 6L;
        g_30 = 8L;
    }
    return l_17;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
