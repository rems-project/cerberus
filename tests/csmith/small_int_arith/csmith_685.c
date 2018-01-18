// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_685.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = 0x2C21L;
static uint32_t g_4 = 18446744073709551614UL;
static uint8_t g_6 = 0xC2L;
static int64_t g_7 = 0x16652D0DA0BDBDF7LL;
static uint32_t g_8 = 0x2282D564L;
static uint32_t g_16 = 5UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int32_t l_3 = 0x2236432AL;
    int8_t l_5 = 0L;
    l_3 |= g_2;
    g_4 = l_3;
    if (l_5)
    { 
        uint64_t l_11 = 18446744073709551614UL;
        int32_t l_14 = 8L;
        g_6 = 0x3A23FE5EL;
        g_8--;
        l_11--;
        l_14 &= 3L;
    }
    else
    { 
        uint16_t l_15 = 1UL;
        l_3 = l_15;
        g_16 &= l_5;
        return l_15;
    }
    return l_3;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
