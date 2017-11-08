// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_478.c
#include "csmith.h"


static long __undefined;



static uint8_t g_2 = 0x03L;
static int32_t g_3 = (-3L);
static int32_t g_12 = (-10L);
static int64_t g_16 = 0x9193C1DE6FC6088BLL;
static int32_t g_17 = 0L;
static int16_t g_18 = 1L;
static int32_t g_22 = 0x59785734L;
static int32_t g_23 = 0x1E6E4042L;
static int32_t g_26 = 0x4B3F4B14L;
static uint32_t g_29 = 0x7279C90EL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int32_t l_4 = (-1L);
    int32_t l_6 = 0x5A1FA147L;
    int32_t l_7 = 0x3CF95751L;
    int32_t l_10 = (-4L);
    int32_t l_13 = 0xF38D927FL;
    int32_t l_15 = 0xFDBD0176L;
    int32_t l_21 = 0x5AEE0CD9L;
    g_3 = g_2;
    l_4 = g_3;
    g_3 ^= l_4;
    if (l_4)
    { 
        int32_t l_5 = 0x5CA9869EL;
        l_5 = g_2;
    }
    else
    { 
        int64_t l_8 = (-1L);
        int32_t l_9 = (-1L);
        int32_t l_11 = 1L;
        int32_t l_14 = 1L;
        int32_t l_19 = 0xAB5C2947L;
        int32_t l_20 = 0xE5849968L;
        int32_t l_24 = (-1L);
        int32_t l_25 = (-9L);
        int32_t l_27 = 0x9BA5E0B2L;
        int32_t l_28 = 0xCE1A812CL;
        g_29++;
    }
    return g_29;
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
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_29, "g_29", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
