// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_077.c
#include "csmith.h"


static long __undefined;



static int32_t g_5 = 0L;
static uint8_t g_16 = 0UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint16_t l_4 = 0xC90AL;
    int32_t l_13 = 0x89F42C60L;
    int32_t l_14 = (-2L);
    int32_t l_17 = 0xF18EE85EL;
    int32_t l_20 = (-1L);
    if ((safe_lshift_func_uint16_t_u_u(((l_4 >= g_5) ^ g_5), 8)))
    { 
        int32_t l_12 = 0x78C007C7L;
        int32_t l_15 = 0x10DD6640L;
        g_5 = l_4;
        l_17 = (((g_16 = (l_15 = ((safe_add_func_int32_t_s_s((l_14 = (((((safe_mul_func_int8_t_s_s(((l_13 = (safe_lshift_func_uint16_t_u_s((0xACL >= 0UL), l_12))) , 1L), g_5)) && g_5) && l_13) , g_5) , l_12)), l_12)) , l_14))) == 18446744073709551610UL) | 0UL);
        g_5 = ((safe_rshift_func_uint16_t_u_s(l_20, 6)) , g_16);
        l_15 ^= (g_5 <= 0L);
    }
    else
    { 
        for (l_4 = 0; (l_4 <= 21); l_4 = safe_add_func_int16_t_s_s(l_4, 3))
        { 
            int16_t l_23 = (-4L);
            return l_23;
        }
    }
    return g_16;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
