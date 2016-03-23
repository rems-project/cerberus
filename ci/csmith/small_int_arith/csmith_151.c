// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_151.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x324EC2E0L;
static uint16_t g_8 = 0x16DBL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int32_t l_7 = 0L;
    int32_t l_12 = 0L;
    int32_t l_17 = 0L;
    for (g_2 = (-27); (g_2 != (-21)); ++g_2)
    { 
        g_8 = (((safe_div_func_int32_t_s_s((7UL & g_2), l_7)) ^ g_2) == g_2);
    }
    l_12 = (((+((safe_lshift_func_uint16_t_u_s((l_7 = ((l_7 == 0xC9EBF495L) > 1L)), l_12)) <= l_12)) >= 0x8D9A2B82C4475EE4LL) == 1UL);
    l_12 = g_8;
    g_2 = (((l_17 &= (safe_mod_func_uint32_t_u_u((((((safe_sub_func_uint32_t_u_u(((l_7 &= l_12) != l_12), l_12)) & 1L) && l_7) ^ g_2) & l_12), g_2))) , g_2) >= 7L);
    return g_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
