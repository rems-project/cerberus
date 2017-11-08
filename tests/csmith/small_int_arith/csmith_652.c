// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_652.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = 0x1BL;
static uint16_t g_5 = 0UL;
static int16_t g_8 = 0L;
static int16_t g_10 = 1L;
static int32_t g_11 = 0L;
static uint64_t g_13 = 0UL;
static int64_t g_20 = (-1L);
static int64_t g_21 = (-10L);
static int8_t g_22 = (-8L);
static int32_t g_24 = 0xD635290CL;
static uint32_t g_27 = 1UL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int64_t l_3 = 1L;
    int32_t l_4 = 0xCB457102L;
    int32_t l_9 = 1L;
    int32_t l_12 = 0x16EFA42BL;
    int32_t l_23 = 0x0A6FF609L;
    int32_t l_25 = 0x9ED02E88L;
    int32_t l_26 = 0L;
    ++g_5;
    if (l_4)
    { 
        uint32_t l_16 = 0x5ED06576L;
        ++g_13;
        l_16 = l_4;
        g_11 = l_12;
        g_11 = l_16;
    }
    else
    { 
        uint64_t l_17 = 18446744073709551610UL;
        l_12 = g_8;
        --l_17;
        return g_2;
    }
    g_27++;
    return l_23;
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
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
