// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_261.c
#include "csmith.h"


static long __undefined;



static uint64_t g_4 = 18446744073709551610UL;
static int64_t g_8 = 0xBB4EBB0CB8CE3E63LL;
static int32_t g_10 = 0L;
static int8_t g_11 = 0x2CL;
static int16_t g_13 = 4L;
static int8_t g_15 = (-1L);
static uint64_t g_17 = 0xD2D91509CF13E13ALL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int8_t l_2 = 3L;
    int32_t l_3 = 1L;
    int32_t l_7 = 0x7E17F759L;
    int32_t l_9 = (-1L);
    int32_t l_12 = (-8L);
    int32_t l_14 = 0L;
    int32_t l_16 = 0xDFE012D2L;
    --g_4;
    --g_17;
    l_9 = (-3L);
    return g_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
