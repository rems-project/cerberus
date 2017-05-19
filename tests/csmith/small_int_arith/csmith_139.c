// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_139.c
#include "csmith.h"


static long __undefined;



static uint64_t g_7 = 18446744073709551614UL;
static uint64_t g_16 = 18446744073709551608UL;
static uint32_t g_23 = 0x9B780F88L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint64_t l_8 = 3UL;
    int32_t l_9 = 1L;
    int8_t l_22 = 1L;
    l_9 = ((safe_sub_func_uint8_t_u_u((safe_rshift_func_uint8_t_u_s((+g_7), g_7)), l_8)) || g_7);
    if (g_7)
        goto lbl_17;
lbl_17:
    g_16 ^= ((safe_mul_func_uint16_t_u_u(((safe_mul_func_uint8_t_u_u(((safe_div_func_uint16_t_u_u((((g_7 > g_7) >= l_8) && l_8), (-1L))) ^ 7UL), g_7)) != g_7), 0x13B2L)) != l_9);
    g_23 ^= ((safe_add_func_int64_t_s_s((safe_add_func_uint16_t_u_u(l_8, 0x0D13L)), 0L)) < l_22);
    return l_22;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
