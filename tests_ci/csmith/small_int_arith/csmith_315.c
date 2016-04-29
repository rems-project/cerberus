// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_315.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 6L;
static int16_t g_3 = 0xB7C7L;
static uint64_t g_13 = 0xFE23A266D210EC32LL;
static uint32_t g_14 = 4294967295UL;
static int64_t g_17 = 0x530A9BCA7B5CF1C9LL;
static int32_t g_21 = 0x1FA4C821L;
static int32_t g_24 = 0x193FE696L;
static int32_t g_26 = 0x37D6C505L;
static int32_t g_27 = (-1L);
static int8_t g_29 = 3L;
static uint32_t g_31 = 0UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int32_t l_10 = 0x4320E32CL;
    int32_t l_22 = 0L;
    int32_t l_23 = (-5L);
    int32_t l_25 = 0L;
    int32_t l_28 = 0L;
    int32_t l_30 = 0xFC5674FAL;
    g_3 &= g_2;
    for (g_2 = 17; (g_2 == 7); g_2 = safe_sub_func_uint16_t_u_u(g_2, 8))
    { 
        l_10 ^= ((safe_sub_func_int32_t_s_s((safe_rshift_func_int16_t_s_s((0x891CL < g_2), g_3)), g_3)) , g_3);
        g_14 = (((safe_lshift_func_uint8_t_u_u((g_13 = g_3), g_2)) , g_3) || 4294967291UL);
        for (l_10 = 0; (l_10 != (-4)); l_10 = safe_sub_func_uint32_t_u_u(l_10, 5))
        { 
            int64_t l_20 = 0x6B42BE197E7C14ABLL;
            g_17 = l_10;
            l_20 &= (safe_sub_func_int16_t_s_s(l_10, g_13));
        }
    }
    g_31--;
    l_30 = (~l_25);
    return g_31;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    transparent_crc(g_29, "g_29", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
