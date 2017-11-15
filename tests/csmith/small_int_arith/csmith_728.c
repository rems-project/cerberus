// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_728.c
#include "csmith.h"


static long __undefined;



static uint8_t g_2 = 1UL;
static int64_t g_5 = 1L;
static int64_t g_6 = 0x90F1D8987F2FB5A5LL;
static uint64_t g_8 = 18446744073709551607UL;
static uint32_t g_11 = 3UL;
static uint32_t g_13 = 4294967288UL;
static uint32_t g_18 = 18446744073709551615UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int16_t l_7 = 0x5C57L;
    int32_t l_17 = 0x062D7BC3L;
    g_2 = 1L;
    for (g_2 = 5; (g_2 < 15); g_2++)
    { 
        int8_t l_12 = (-1L);
        g_8++;
        g_11 = 2L;
        l_12 = 0x451D52AAL;
    }
    if (g_5)
    { 
        uint32_t l_16 = 1UL;
        g_13--;
        return l_16;
    }
    else
    { 
        int64_t l_19 = (-4L);
        uint32_t l_20 = 1UL;
        l_17 = l_7;
        g_18 |= g_8;
        l_20--;
    }
    return g_18;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
