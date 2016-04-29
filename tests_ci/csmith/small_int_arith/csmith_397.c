// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_397.c
#include "csmith.h"


static long __undefined;



static int8_t g_11 = 0x67L;
static int8_t g_22 = (-1L);



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint32_t l_2 = 0xB9102071L;
    int32_t l_14 = 0xEC0351A9L;
    if (l_2)
    { 
        int64_t l_12 = 0x3880E033C2251554LL;
        uint32_t l_13 = 0UL;
        int32_t l_15 = 0L;
        int8_t l_20 = 0x4CL;
        int32_t l_21 = 0xA2CA335CL;
        l_15 = (safe_mod_func_int8_t_s_s(((safe_mul_func_uint8_t_u_u((((safe_sub_func_int64_t_s_s((safe_add_func_int64_t_s_s((((((g_11 & g_11) ^ 0x2A10L) != 0xB74CL) , g_11) ^ l_12), g_11)), l_12)) , l_13) <= 0UL), l_14)) <= l_2), l_13));
        l_21 |= (safe_lshift_func_int8_t_s_s((safe_mul_func_int8_t_s_s(l_15, l_20)), g_11));
        l_21 = ((-4L) && g_11);
        g_22 = (g_11 && l_2);
    }
    else
    { 
        uint32_t l_23 = 0xD47030FCL;
        return l_23;
    }
    return g_22;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
