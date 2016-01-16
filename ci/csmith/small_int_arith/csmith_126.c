// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_126.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = 0x67A8L;
static int8_t g_9 = 0x67L;
static int16_t g_11 = 0xA110L;
static uint32_t g_17 = 1UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_3 = 0xD7953644L;
    int32_t l_4 = (-1L);
    int32_t l_5 = (-1L);
    uint64_t l_6 = 0x1AB6EC79CF1813F1LL;
    int32_t l_10 = (-2L);
    int32_t l_12 = 0x1E4F1F13L;
    int32_t l_13 = (-1L);
    int32_t l_14 = (-10L);
    int32_t l_15 = 0x6F97812AL;
    int32_t l_16 = (-5L);
    l_3 = (65530UL ^ g_2);
    l_6--;
    --g_17;
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
