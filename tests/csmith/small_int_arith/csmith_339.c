// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_339.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 0UL;
static uint8_t g_10 = 1UL;
static uint16_t g_17 = 0x3D06L;
static uint8_t g_19 = 0x7BL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_5 = 0x3C69AED23B6182EALL;
    uint32_t l_18 = 1UL;
    int32_t l_20 = 1L;
    l_5 |= (safe_mul_func_uint8_t_u_u(g_4, g_4));
    l_20 = (g_19 = (safe_lshift_func_int16_t_s_s((safe_rshift_func_int8_t_s_u(((((g_10++) >= (safe_rshift_func_uint16_t_u_u((safe_mul_func_uint16_t_u_u(((g_17 ^= l_5) || g_4), l_5)), 9))) , 0xB8F6L) || g_4), 1)), l_18)));
    return g_10;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
