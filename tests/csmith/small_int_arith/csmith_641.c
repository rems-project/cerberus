// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_641.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 1L;
static uint64_t g_3 = 0x871C7BF0B96CA2CBLL;
static int32_t g_7 = 9L;
static int8_t g_11 = 0x6FL;
static int8_t g_12 = (-1L);
static int64_t g_14 = 0x3BFA32A17D0B0A35LL;
static int32_t g_16 = 1L;
static uint64_t g_20 = 18446744073709551611UL;
static int32_t g_24 = 0xDBDAE4F9L;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int32_t l_4 = (-9L);
    int32_t l_5 = (-9L);
    int32_t l_6 = 0x085C9E53L;
    int32_t l_13 = 0xCF4A4163L;
    int64_t l_15 = 1L;
    uint32_t l_17 = 18446744073709551610UL;
    g_3 = g_2;
    l_4 |= g_3;
    if (g_3)
    { 
        int32_t l_8 = 0L;
        int32_t l_9 = 0x2DAAB72BL;
        int32_t l_10 = 0L;
        ++l_17;
        l_13 = l_6;
        --g_20;
    }
    else
    { 
        uint32_t l_23 = 8UL;
        l_23 = l_13;
        g_24 &= l_15;
    }
    return g_3;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
