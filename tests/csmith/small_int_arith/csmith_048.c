// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_048.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 5L;
static int32_t g_8 = (-1L);
static int16_t g_9 = 0L;
static int32_t g_10 = 0x035C5735L;
static uint64_t g_11 = 0x4D8A94B2AB76D609LL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int8_t l_7 = 2L;
    for (g_2 = (-11); (g_2 >= 27); ++g_2)
    { 
        int16_t l_26 = (-4L);
        int32_t l_32 = 0x0B807220L;
        if ((l_7 = (safe_lshift_func_uint8_t_u_s(1UL, 2))))
        { 
            uint16_t l_25 = 0x0051L;
            g_11--;
            for (g_8 = (-20); (g_8 > (-10)); g_8 = safe_add_func_uint16_t_u_u(g_8, 1))
            { 
                if ((safe_sub_func_int32_t_s_s((g_10 = ((safe_add_func_uint32_t_u_u(((safe_mod_func_int32_t_s_s((((((safe_unary_minus_func_int8_t_s(((safe_rshift_func_int8_t_s_u(l_25, l_25)) != l_26))) , g_10) >= 3L) ^ 0x3D87E3BCL) != g_11), g_9)) != l_7), g_8)) ^ l_25)), 0L)))
                { 
                    uint64_t l_31 = 0UL;
                    g_10 = ((safe_lshift_func_uint8_t_u_s((((((safe_add_func_uint8_t_u_u(((l_25 == g_11) == g_11), g_10)) , 1UL) || g_2) <= 4294967295UL) >= 1UL), l_31)) | 5L);
                }
                else
                { 
                    return g_8;
                }
                l_32 = g_9;
            }
        }
        else
        { 
            return l_32;
        }
        g_10 |= (g_2 & 0x78B7L);
        g_10 ^= l_26;
    }
    return l_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
