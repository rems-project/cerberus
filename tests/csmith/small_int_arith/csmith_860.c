// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_860.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 1UL;
static int16_t g_5 = 0x4351L;
static uint32_t g_10 = 0xFBA1A4D6L;
static int32_t g_11 = (-10L);
static int16_t g_12 = 0x9B38L;
static int8_t g_13 = 0xE4L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint64_t l_6 = 0UL;
    if (g_2)
    { 
        int32_t l_3 = 0x0FE6E324L;
        int32_t l_4 = 0xCCCE1E2CL;
        --l_6;
        return l_4;
    }
    else
    { 
        int16_t l_9 = (-1L);
        g_10 = l_9;
    }
    g_11 = g_10;
    g_12 = g_2;
    return g_13;
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
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
