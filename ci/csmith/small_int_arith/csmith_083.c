// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_083.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = 0x41B3L;
static int32_t g_7 = 0x1464F16EL;
static uint64_t g_20 = 0x2F20920A6FF609D7LL;
static int32_t g_42 = 1L;
static int16_t g_50 = 0x6E99L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_3 = 4294967289UL;
    uint8_t l_8 = 0xBFL;
    int32_t l_16 = 0xA652065CL;
    int32_t l_17 = (-1L);
    int16_t l_33 = 0L;
    if (g_2)
    { 
        return l_3;
    }
    else
    { 
        int8_t l_6 = 0L;
        int32_t l_18 = 8L;
        int16_t l_43 = (-8L);
        g_7 = ((safe_rshift_func_uint8_t_u_s((g_2 , 248UL), g_2)) | l_6);
        l_8 = l_3;
        for (g_2 = 0; (g_2 != 28); g_2++)
        { 
            int16_t l_19 = (-3L);
            if (g_7)
            { 
                int64_t l_15 = 0x9B2E4145C1747346LL;
                l_15 &= (safe_rshift_func_uint8_t_u_u((safe_add_func_uint64_t_u_u(g_2, g_7)), g_2));
                if (g_7)
                    break;
            }
            else
            { 
                if (l_3)
                { 
                    uint32_t l_25 = 3UL;
                    g_20++;
                    if ((((safe_div_func_uint32_t_u_u(g_2, l_25)) ^ g_2) == l_18))
                    { 
                        int8_t l_26 = (-4L);
                        g_7 = (l_26 , l_19);
                    }
                    else
                    { 
                        return g_20;
                    }
                    return g_20;
                }
                else
                { 
                    g_7 = (safe_mod_func_uint64_t_u_u((safe_add_func_uint16_t_u_u(65529UL, l_19)), g_20));
                }
                l_33 |= (((safe_mul_func_uint8_t_u_u(g_20, g_2)) , 0x8F9611CA4B38B4B7LL) | l_6);
                l_18 = ((((safe_sub_func_uint16_t_u_u((((((safe_add_func_uint16_t_u_u((safe_unary_minus_func_uint16_t_u((((safe_unary_minus_func_int32_t_s(((safe_sub_func_uint32_t_u_u(((g_42 = g_20) , g_20), g_20)) <= g_2))) || 4L) <= l_18))), l_43)) & g_7) <= l_17) >= g_20) > l_16), 0x98A9L)) & (-1L)) , l_18) <= g_7);
                for (l_6 = 3; (l_6 < 2); --l_6)
                { 
                    for (l_19 = 0; (l_19 != (-20)); --l_19)
                    { 
                        return l_18;
                    }
                    return l_19;
                }
            }
        }
    }
    for (l_16 = 0; (l_16 <= (-23)); l_16 = safe_sub_func_int8_t_s_s(l_16, 2))
    { 
        uint8_t l_51 = 0x54L;
        g_50 |= (g_7 || 4294967293UL);
        if ((0x8BF9CC53A0DCB3DFLL ^ 18446744073709551615UL))
        { 
            return l_51;
        }
        else
        { 
            g_7 = 0x30F13E0CL;
        }
    }
    for (l_33 = (-16); (l_33 < (-19)); l_33--)
    { 
        int64_t l_54 = (-1L);
        int32_t l_55 = 8L;
        uint8_t l_56 = 7UL;
        l_55 &= l_54;
        if (((((l_55 ^= g_2) & l_56) > (-9L)) < g_20))
        { 
            int32_t l_61 = (-4L);
            for (g_42 = 1; (g_42 == (-22)); g_42 = safe_sub_func_uint64_t_u_u(g_42, 5))
            { 
                l_61 = (g_7 ^= (safe_add_func_int32_t_s_s(0x18344157L, g_50)));
            }
            g_7 = (safe_mul_func_int16_t_s_s(1L, 0L));
        }
        else
        { 
            uint32_t l_64 = 0x4CD5900AL;
            if (g_2)
                break;
            l_64--;
            l_55 = l_3;
        }
    }
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_42, "g_42", print_hash_value);
    transparent_crc(g_50, "g_50", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
