// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_117.c
#include "csmith.h"


static long __undefined;



static int16_t g_4 = (-3L);
static int32_t g_7 = 8L;
static int32_t g_10 = (-9L);
static uint32_t g_27 = 0xC556123DL;
static uint32_t g_28 = 0x36D0C11EL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint64_t l_15 = 0UL;
    int32_t l_20 = (-3L);
    g_4 = (safe_mul_func_int16_t_s_s(1L, 1UL));
    for (g_4 = (-2); (g_4 == (-28)); g_4 = safe_sub_func_int64_t_s_s(g_4, 9))
    { 
        int32_t l_16 = (-1L);
        int32_t l_41 = (-7L);
        for (g_7 = (-22); (g_7 < 12); g_7++)
        { 
            int32_t l_19 = (-6L);
            for (g_10 = (-28); (g_10 < 23); ++g_10)
            { 
                l_16 &= (safe_lshift_func_uint8_t_u_u(l_15, 1));
            }
            l_20 ^= ((safe_div_func_int32_t_s_s(g_7, l_15)) == l_19);
            g_27 = (g_10 = ((safe_add_func_int64_t_s_s((safe_mul_func_int16_t_s_s((safe_sub_func_uint64_t_u_u((g_10 , l_16), l_15)), g_4)), l_19)) < l_15));
            --g_28;
        }
        for (g_7 = 0; (g_7 != 25); ++g_7)
        { 
            uint16_t l_40 = 0x9A48L;
            g_10 = l_16;
            for (g_28 = (-11); (g_28 < 13); g_28 = safe_add_func_int8_t_s_s(g_28, 7))
            { 
                int32_t l_39 = (-3L);
                g_10 = ((l_41 = ((safe_sub_func_uint8_t_u_u((safe_lshift_func_uint8_t_u_s(l_39, 7)), l_40)) != l_20)) || g_28);
            }
        }
    }
    return g_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
