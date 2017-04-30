// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_043.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x5B9B55BBL;
static uint32_t g_9 = 0xC5021C3AL;
static uint64_t g_30 = 0x5A165F5C9B8DB370LL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint8_t l_10 = 250UL;
    int32_t l_40 = 0x3439FCB6L;
    int32_t l_41 = 1L;
    for (g_2 = 0; (g_2 < 2); ++g_2)
    { 
        int32_t l_7 = 0xA73D2D67L;
        int32_t l_8 = (-1L);
        g_9 = (safe_add_func_int64_t_s_s((l_7 = 0x0025260417BE1879LL), l_8));
        l_8 |= g_2;
        if (l_10)
            break;
        for (l_7 = 0; (l_7 >= 10); l_7 = safe_add_func_int32_t_s_s(l_7, 4))
        { 
            for (l_10 = 0; (l_10 <= 34); ++l_10)
            { 
                int8_t l_17 = 0x6FL;
                l_8 = (safe_sub_func_uint32_t_u_u(l_17, g_9));
            }
        }
    }
    for (g_2 = (-7); (g_2 != 8); g_2++)
    { 
        uint32_t l_26 = 7UL;
        int32_t l_27 = 0xF0A0CD95L;
        int32_t l_37 = 0x36C745D0L;
        l_27 = (safe_add_func_int32_t_s_s((safe_mod_func_uint8_t_u_u((((((safe_rshift_func_uint8_t_u_u(l_26, 7)) > 0xC266D8FFL) && 0xD3BEL) , g_9) , 0xCEL), 0x76L)), l_10));
        g_30 = ((safe_mod_func_uint64_t_u_u((0x3DL != g_2), 18446744073709551615UL)) , 0L);
        if ((((safe_lshift_func_int8_t_s_s((safe_sub_func_int8_t_s_s((((safe_lshift_func_int16_t_s_s(((-7L) != (-3L)), 14)) & 0xFD090D790F958483LL) , g_9), g_2)), 7)) < g_30) , l_10))
        { 
            l_27 ^= 0xAF03FA9AL;
            return g_2;
        }
        else
        { 
            l_37 &= (l_27 = l_10);
        }
    }
    l_41 |= ((safe_sub_func_uint8_t_u_u(255UL, l_40)) <= l_10);
    return g_30;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
