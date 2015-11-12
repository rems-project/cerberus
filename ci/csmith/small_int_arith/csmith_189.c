// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_189.c
#include "csmith.h"


static long __undefined;



static int8_t g_3 = 0xDAL;
static int16_t g_14 = 0L;
static int32_t g_18 = 0x2894FF54L;
static uint16_t g_21 = 0x9964L;
static int16_t g_26 = 0x36C9L;
static uint32_t g_31 = 5UL;
static uint8_t g_42 = 8UL;
static uint32_t g_48 = 3UL;
static int16_t g_50 = 0x4BFCL;
static uint64_t g_51 = 1UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint32_t l_2 = 4294967295UL;
    int16_t l_19 = 1L;
    uint32_t l_47 = 0x7D231D57L;
    int32_t l_52 = 0x8E4446CAL;
    g_3 |= l_2;
    for (l_2 = 0; (l_2 != 47); l_2++)
    { 
        uint32_t l_10 = 0UL;
        int64_t l_39 = 5L;
        int32_t l_40 = 7L;
        for (g_3 = 0; (g_3 < 23); g_3 = safe_add_func_int8_t_s_s(g_3, 1))
        { 
            uint8_t l_13 = 0xF3L;
            int32_t l_20 = 0x30B91EE4L;
            if ((safe_mul_func_uint16_t_u_u(1UL, g_3)))
            { 
                if (g_3)
                    break;
                l_10 ^= l_2;
            }
            else
            { 
                int64_t l_27 = 0xC068927649690B28LL;
                int32_t l_28 = 4L;
                l_13 = ((((((safe_mod_func_int8_t_s_s(g_3, 0x17L)) && 18446744073709551615UL) > l_2) & 0xE4L) ^ 0xC3L) && g_3);
                g_14 |= g_3;
                if (g_14)
                { 
                    if (g_14)
                        break;
                    if (l_10)
                        continue;
                }
                else
                { 
                    uint64_t l_17 = 0x9A130DFDDAE974CALL;
                    l_19 = ((g_18 = ((safe_div_func_int64_t_s_s(g_3, g_14)) , l_17)) , g_3);
                    if (g_3)
                        continue;
                    g_21 = ((l_20 &= (g_18 , g_3)) || g_3);
                    g_26 = (safe_div_func_int8_t_s_s((((safe_lshift_func_uint8_t_u_s(((g_14 <= 1UL) , 1UL), l_19)) == 4294967294UL) && 0xFFA898CBDB62B2FALL), l_10));
                }
                l_28 = (l_19 && l_27);
            }
        }
        for (l_10 = (-21); (l_10 != 40); l_10++)
        { 
            uint8_t l_38 = 253UL;
            int32_t l_41 = (-1L);
            g_31 = l_10;
            if ((safe_sub_func_uint16_t_u_u((safe_lshift_func_uint16_t_u_u(((safe_lshift_func_uint16_t_u_u((((g_18 ^ l_38) | 1L) >= l_38), 4)) >= (-1L)), l_39)), 0xB265L)))
            { 
                if (g_3)
                    break;
                ++g_42;
            }
            else
            { 
                int32_t l_49 = 0x6833686AL;
                g_48 = ((((safe_div_func_uint64_t_u_u(l_47, l_2)) , 0x4CA6L) >= 65530UL) | l_39);
                g_50 = l_49;
            }
            g_51 = ((l_10 <= g_31) & g_21);
            if (g_14)
                break;
        }
        l_52 &= ((g_3 = ((0x0BDEC7E1L && l_10) >= 0xFF9BDEFAB77C19C5LL)) != 0x8BL);
    }
    return g_31;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    transparent_crc(g_42, "g_42", print_hash_value);
    transparent_crc(g_48, "g_48", print_hash_value);
    transparent_crc(g_50, "g_50", print_hash_value);
    transparent_crc(g_51, "g_51", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
