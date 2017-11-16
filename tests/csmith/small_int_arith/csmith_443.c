// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_443.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = 0L;
static uint32_t g_11 = 0x55CC25BFL;
static int16_t g_14 = 0x1B68L;
static int16_t g_18 = (-8L);
static int64_t g_19 = (-6L);
static uint64_t g_20 = 1UL;
static uint32_t g_21 = 0UL;
static uint64_t g_22 = 0xD8AF8716B5B3847DLL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint64_t l_3 = 18446744073709551606UL;
    int32_t l_9 = 0xC34EEA2AL;
    int32_t l_10 = 0x5653D423L;
    l_3++;
    for (l_3 = (-21); (l_3 < 39); ++l_3)
    { 
        int32_t l_8 = 0x80C170CDL;
        l_8 = g_2;
    }
    g_11++;
    if (l_10)
    { 
        uint8_t l_15 = 0UL;
        l_15++;
        g_18 = l_15;
        g_19 = l_15;
        g_20 = l_10;
    }
    else
    { 
        int64_t l_23 = 0x953E80C6548AAB56LL;
        int32_t l_24 = 0xFEAE2151L;
        g_21 |= g_2;
        g_22 = g_2;
        l_24 = l_23;
        l_9 = g_22;
    }
    return l_10;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
