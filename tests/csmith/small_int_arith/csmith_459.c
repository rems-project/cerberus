// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_459.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0UL;
static uint32_t g_4 = 2UL;
static int16_t g_5 = (-1L);
static uint64_t g_6 = 1UL;
static int8_t g_7 = 0xE0L;
static int8_t g_10 = 0x2BL;
static int32_t g_11 = 0xEDCA8FECL;
static int8_t g_12 = 0x12L;
static int8_t g_14 = 0x66L;
static int64_t g_15 = 1L;
static uint32_t g_16 = 0x7AB6DAD8L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_3 = 6L;
    int8_t l_13 = (-10L);
    g_2 = (-6L);
    if (l_3)
    { 
        return g_4;
    }
    else
    { 
        g_5 &= l_3;
        g_6 = g_4;
    }
    g_7 ^= 0x10FECAFEL;
    for (g_7 = 0; (g_7 != 28); g_7++)
    { 
        ++g_16;
        if (g_10)
            break;
        g_11 = 0x7863718BL;
    }
    return l_13;
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
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
