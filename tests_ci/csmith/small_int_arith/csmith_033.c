// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_033.c
#include "csmith.h"


static long __undefined;



static int64_t g_15 = 0L;
static int32_t g_16 = (-2L);



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint8_t l_14 = 2UL;
    int32_t l_17 = 0xC1DA7BC9L;
    int8_t l_20 = 0x0EL;
    l_17 = (safe_mod_func_uint8_t_u_u((safe_sub_func_uint32_t_u_u((safe_rshift_func_int16_t_s_s((safe_add_func_uint16_t_u_u(((safe_add_func_int16_t_s_s((safe_div_func_int16_t_s_s(((g_15 = ((l_14 ^ l_14) | (-8L))) & 0L), l_14)), l_14)) , l_14), 65535UL)), 11)), (-1L))), g_16));
    l_17 = ((safe_sub_func_uint64_t_u_u(l_20, 0x6CD333563700168ALL)) >= (-1L));
    return g_16;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
