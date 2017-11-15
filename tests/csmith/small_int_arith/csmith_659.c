// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_659.c
#include "csmith.h"


static long __undefined;



static uint32_t g_5 = 0x4EE7D214L;
static int32_t g_8 = 0x069F30CCL;
static uint32_t g_9 = 0xFAC12265L;
static uint16_t g_10 = 0xB239L;
static int64_t g_15 = (-1L);
static int32_t g_17 = 0x0A98CEEFL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int32_t l_2 = 0xE48D327CL;
    int32_t l_3 = (-5L);
    int32_t l_4 = 0x665683C8L;
    const uint16_t l_18 = 0xB76EL;
    g_5--;
    if (g_5)
    { 
        g_8 = 0xA971867BL;
        g_9 = l_2;
        g_10++;
    }
    else
    { 
        uint64_t l_13 = 0x9C45C1D102278213LL;
        uint32_t l_14 = 0x821342F3L;
        l_2 = g_9;
        l_13 = l_2;
        l_3 = g_10;
        l_3 = l_14;
    }
    if (l_2)
    { 
        uint64_t l_16 = 18446744073709551615UL;
        g_15 = g_8;
        g_17 = l_16;
        g_17 = l_18;
        g_17 &= (-1L);
    }
    else
    { 
        uint8_t l_19 = 5UL;
        l_2 = 0xD8D955A6L;
        l_2 = l_4;
        l_19--;
    }
    l_2 ^= 0x25FC1C57L;
    return g_17;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
