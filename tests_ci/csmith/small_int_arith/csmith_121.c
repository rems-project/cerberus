// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_121.c
#include "csmith.h"


static long __undefined;



static int32_t g_7 = (-1L);
static uint64_t g_27 = 0x967684ABF0A64418LL;
static uint64_t g_38 = 0x81FDF20BE86DE1F1LL;
static int8_t g_40 = 0x5CL;
static uint16_t g_41 = 0xA064L;
static uint32_t g_64 = 0xB032F891L;
static int16_t g_70 = 0x2B0DL;
static uint8_t g_71 = 250UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint16_t l_6 = 1UL;
    int32_t l_10 = 0L;
    int32_t l_14 = (-1L);
    uint16_t l_69 = 4UL;
    g_7 |= (safe_rshift_func_uint8_t_u_u((safe_mod_func_uint64_t_u_u(l_6, l_6)), 3));
    l_10 = ((safe_rshift_func_uint16_t_u_u((g_7 < (-1L)), 10)) | g_7);
    for (l_6 = 6; (l_6 <= 12); ++l_6)
    { 
        int8_t l_13 = 1L;
        int32_t l_26 = 1L;
        if (l_13)
            break;
        if ((g_7 = (-1L)))
        { 
            int64_t l_23 = 0xB3F4B14151C8B9BALL;
            int32_t l_24 = (-5L);
            uint32_t l_46 = 18446744073709551610UL;
            if (((l_10 &= g_7) != 8UL))
            { 
                uint16_t l_49 = 0xF69FL;
                int32_t l_50 = 0x1B015869L;
                int64_t l_55 = 0L;
                if ((((l_14 = ((((l_13 && g_7) > g_7) ^ 0x3C1DE6FCL) == l_10)) ^ g_7) , g_7))
                { 
                    int8_t l_15 = 0x68L;
                    int32_t l_25 = 0xCD953295L;
                    if (l_15)
                    { 
                        int32_t l_22 = 0xC512DC6DL;
                        g_7 = (!((safe_add_func_uint16_t_u_u(((safe_mul_func_uint16_t_u_u((l_23 = (+l_22)), 0x7AB6L)) > l_24), g_7)) , l_24));
                    }
                    else
                    { 
                        ++g_27;
                        l_25 |= (safe_lshift_func_uint8_t_u_u(l_23, 1));
                    }
                    if (((safe_mod_func_int32_t_s_s(4L, l_6)) || l_6))
                    { 
                        g_38 |= (safe_lshift_func_uint16_t_u_u((safe_div_func_int64_t_s_s(((l_13 == l_15) <= g_7), 0x9097D93CBFB41CE0LL)), g_27));
                    }
                    else
                    { 
                        int8_t l_39 = (-5L);
                        l_39 &= (g_7 = ((g_27 != (-6L)) | g_27));
                        ++g_41;
                        l_46 = (safe_sub_func_int64_t_s_s((l_26 & l_23), l_26));
                        l_50 |= ((safe_add_func_uint32_t_u_u((l_49 != g_7), g_38)) != g_7);
                    }
                }
                else
                { 
                    int8_t l_53 = (-2L);
                    int32_t l_54 = 0x5EFF85A0L;
                    g_7 |= g_41;
                    l_24 = (((safe_lshift_func_int16_t_s_s(g_27, 0)) == 0xE235BD639B6AF4A9LL) >= g_40);
                    l_54 = l_53;
                    if (l_55)
                        break;
                }
                g_7 |= (safe_div_func_uint16_t_u_u(((safe_rshift_func_uint8_t_u_s(((l_50 = 0x81CFL) ^ 0xA8A5L), g_38)) , 6UL), g_40));
                l_24 = (safe_sub_func_int32_t_s_s((l_10 |= l_23), l_14));
                l_24 ^= (((safe_lshift_func_int16_t_s_u((g_64 ^= l_14), 9)) >= g_7) , g_40);
            }
            else
            { 
                l_10 = ((g_64 || g_7) || 0xE1L);
            }
            return l_13;
        }
        else
        { 
            g_7 = (safe_lshift_func_uint16_t_u_u((safe_mul_func_int8_t_s_s(((l_69 = (-1L)) | g_7), l_13)), g_38));
        }
        g_7 ^= (l_13 == g_64);
        if (g_7)
            continue;
    }
    --g_71;
    return g_27;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    transparent_crc(g_40, "g_40", print_hash_value);
    transparent_crc(g_41, "g_41", print_hash_value);
    transparent_crc(g_64, "g_64", print_hash_value);
    transparent_crc(g_70, "g_70", print_hash_value);
    transparent_crc(g_71, "g_71", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
