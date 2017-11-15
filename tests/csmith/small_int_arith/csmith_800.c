// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_800.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0x894801897A4A12B5LL;
static int8_t g_3 = 0x55L;
static int32_t g_4 = 0L;
static int32_t g_11 = 2L;
static int64_t g_14 = 0x8E045DCEFBDE283BLL;
static int32_t g_15 = 0L;
static int64_t g_23 = 0x4E62B5009892657CLL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int32_t l_9 = 0xBA75A592L;
    int32_t l_13 = 0x44ADCA1AL;
    int32_t l_16 = 0xB6046E74L;
    int32_t l_17 = (-9L);
    uint64_t l_20 = 0x374489B467BB1A88LL;
    uint16_t l_26 = 0x0971L;
    if (g_2)
    { 
        g_3 = g_2;
        g_4 = 0x9D19AC19L;
        g_4 ^= 1L;
        return g_4;
    }
    else
    { 
        uint16_t l_5 = 0x289AL;
        int32_t l_8 = 0xB101AAE4L;
        ++l_5;
        l_8 = g_4;
        g_4 = g_3;
        g_4 ^= 0x505B0BB8L;
    }
    l_9 = g_2;
    if (g_4)
    { 
        int32_t l_10 = 0L;
        int32_t l_12 = 0xB06C0E26L;
        int32_t l_18 = 0x4A71A6E4L;
        int32_t l_19 = 0x6EFE0CD1L;
        l_20++;
        g_11 = 0L;
    }
    else
    { 
        int8_t l_24 = 0x27L;
        int32_t l_25 = 0x396D56A4L;
        g_4 = g_4;
        g_11 = g_2;
        ++l_26;
    }
    if (l_26)
    { 
        g_11 ^= 1L;
    }
    else
    { 
        g_4 |= (-6L);
    }
    return l_20;
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
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
