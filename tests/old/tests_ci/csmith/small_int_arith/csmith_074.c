// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_074.c
#include "csmith.h"


static long __undefined;



static int32_t g_11 = (-1L);
static uint16_t g_15 = 0xA421L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint8_t l_12 = 255UL;
    int64_t l_13 = 0x33880E033C225155LL;
    int32_t l_14 = 1L;
    g_15 ^= ((safe_lshift_func_uint16_t_u_u((safe_mod_func_int64_t_s_s((l_14 = (safe_div_func_int16_t_s_s((((((safe_lshift_func_int16_t_s_u((safe_unary_minus_func_int8_t_s((g_11 < l_12))), 2)) != l_12) <= 8L) ^ (-1L)) == l_12), l_13))), l_12)), l_12)) , l_13);
    return g_15;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
