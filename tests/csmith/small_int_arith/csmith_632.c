// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_632.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = (-1L);
static int64_t g_5 = (-3L);
static uint8_t g_10 = 0x5EL;
static int8_t g_13 = 0xA9L;
static int32_t g_14 = 0L;
static int64_t g_15 = 0x97812A3CC92EA21ELL;
static int32_t g_16 = 0x2B96CE02L;
static int8_t g_17 = 5L;
static int64_t g_18 = 0x863CC1DAB9737E0DLL;
static uint64_t g_19 = 0x2395E2DE4BF748DCLL;
static int64_t g_22 = 0x3C017F215A60915BLL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint32_t l_3 = 0x6BACD795L;
    int32_t l_4 = 0xA485BF25L;
    int32_t l_9 = 0L;
    uint16_t l_23 = 65535UL;
    if (g_2)
    { 
        int8_t l_6 = (-8L);
        int32_t l_7 = 0L;
        int32_t l_8 = (-6L);
        l_3 = g_2;
        g_10--;
        g_13 = l_9;
        g_14 = 0x13B01D91L;
    }
    else
    { 
        g_19--;
    }
    g_22 = l_4;
    l_9 ^= l_4;
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
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
