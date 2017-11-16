// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_485.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 1L;
static uint16_t g_3 = 0x9763L;
static uint16_t g_9 = 0UL;
static int32_t g_10 = 5L;
static uint16_t g_12 = 65526UL;
static uint32_t g_13 = 0UL;
static uint16_t g_17 = 0x748DL;
static int32_t g_18 = 0x3C017F21L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int64_t l_7 = 0x25CBD94543BEB716LL;
    int32_t l_8 = (-2L);
    const uint8_t l_11 = 0x2EL;
    int32_t l_20 = 0L;
    --g_3;
    if (g_2)
    { 
        int8_t l_6 = (-1L);
        l_7 = l_6;
        l_8 = g_2;
        l_8 = 8L;
        l_8 ^= g_2;
    }
    else
    { 
        g_9 ^= l_8;
        g_10 = l_8;
    }
    if (l_11)
    { 
        int64_t l_16 = 0L;
        g_12 = g_3;
        g_13++;
        l_16 = g_3;
    }
    else
    { 
        uint64_t l_19 = 18446744073709551615UL;
        g_17 |= l_8;
        g_18 = 1L;
        l_20 = l_19;
    }
    return l_11;
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
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
