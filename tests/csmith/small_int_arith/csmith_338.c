// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_338.c
#include "csmith.h"


static long __undefined;



static uint32_t g_7 = 0xF82FF40FL;
static uint8_t g_9 = 246UL;
static int64_t g_10 = (-1L);
static int32_t g_11 = 0x60CBEB96L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint64_t l_6 = 0xCE9D05BA772304B2LL;
    int32_t l_8 = 1L;
    uint16_t l_12 = 0x5725L;
    g_9 = (safe_mod_func_uint64_t_u_u((l_8 = (safe_mul_func_int16_t_s_s(l_6, g_7))), g_7));
    g_10 = (((l_8 && 1UL) <= 0x1FL) , l_6);
    l_12++;
    return g_9;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
