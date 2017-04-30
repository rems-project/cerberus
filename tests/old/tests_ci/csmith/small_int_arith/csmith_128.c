// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_128.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-9L);
static uint64_t g_6 = 1UL;
static int16_t g_21 = (-1L);
static uint64_t g_23 = 0x20578CCA69919C44LL;
static int64_t g_37 = 1L;
static uint16_t g_49 = 1UL;
static int8_t g_55 = 0xDFL;
static int16_t g_56 = 1L;
static uint16_t g_57 = 8UL;
static uint16_t g_64 = 65535UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_5 = (-1L);
    int32_t l_26 = 0x305ABA9AL;
    int32_t l_38 = 0xE3E4F6F4L;
    for (g_2 = 18; (g_2 != (-26)); g_2--)
    { 
        uint16_t l_16 = 1UL;
        int32_t l_22 = 6L;
        g_6 = (g_2 == l_5);
        if (((safe_unary_minus_func_int64_t_s((safe_mod_func_int64_t_s_s((safe_add_func_uint64_t_u_u(((safe_lshift_func_int16_t_s_u(((((l_16 = (safe_rshift_func_uint16_t_u_u((g_6 , 65535UL), 0))) <= 0x6160CBEB969161D5LL) < g_2) < l_5), g_2)) , l_16), g_2)), l_5)))) , l_5))
        { 
            int32_t l_35 = 0x69A0165DL;
            int32_t l_54 = 0x85B5F732L;
            l_22 = ((safe_mod_func_int32_t_s_s(((safe_lshift_func_uint16_t_u_s((g_21 ^= g_2), 12)) , 0xF1E5C8A5L), g_6)) , g_21);
            g_23 = g_21;
            if ((((safe_mul_func_int16_t_s_s(g_6, 1UL)) , g_2) , 0x8110CBBBL))
            { 
                l_26 = (g_23 ^ g_23);
            }
            else
            { 
                uint32_t l_29 = 4294967291UL;
                for (l_5 = 0; (l_5 != (-17)); l_5 = safe_sub_func_int32_t_s_s(l_5, 3))
                { 
                    int32_t l_34 = 0x7A557527L;
                    int32_t l_36 = 0x71603728L;
                    uint32_t l_39 = 0xA3D58E56L;
                    int8_t l_48 = 7L;
                    if (((++l_29) , (((safe_lshift_func_uint8_t_u_u((g_2 <= l_29), l_34)) < 0x69L) <= g_21)))
                    { 
                        --l_39;
                    }
                    else
                    { 
                        g_49 = (safe_lshift_func_uint8_t_u_u((((safe_lshift_func_int16_t_s_s(((safe_mul_func_int16_t_s_s(2L, l_39)) == l_16), l_48)) , (-5L)) <= 4294967287UL), l_35));
                        l_54 |= (safe_div_func_uint16_t_u_u(((safe_mod_func_int64_t_s_s((g_49 || 5UL), (-1L))) & g_49), g_2));
                        g_56 |= ((g_55 = g_21) , g_55);
                    }
                }
                if (l_22)
                    continue;
            }
        }
        else
        { 
            return g_49;
        }
        g_57++;
    }
    g_2 ^= 1L;
    g_2 = (safe_mod_func_int8_t_s_s(((safe_rshift_func_int16_t_s_u(((((g_64 < g_56) , 7L) ^ 0L) <= g_64), l_5)) && (-1L)), 253UL));
    return g_6;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_37, "g_37", print_hash_value);
    transparent_crc(g_49, "g_49", print_hash_value);
    transparent_crc(g_55, "g_55", print_hash_value);
    transparent_crc(g_56, "g_56", print_hash_value);
    transparent_crc(g_57, "g_57", print_hash_value);
    transparent_crc(g_64, "g_64", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
