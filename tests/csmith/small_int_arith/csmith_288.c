// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_288.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 0xC184C506L;
static uint8_t g_14 = 255UL;
static uint16_t g_20 = 0x9DF9L;
static int16_t g_26 = 0x91E6L;
static uint16_t g_27 = 0x4C9DL;
static uint64_t g_34 = 18446744073709551612UL;
static int64_t g_39 = 1L;
static uint32_t g_42 = 0UL;
static uint16_t g_45 = 0x3D49L;
static int8_t g_46 = (-1L);
static uint16_t g_61 = 0x4F7BL;
static int16_t g_63 = (-2L);



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_2 = (-1L);
    int32_t l_8 = 0x25FA5FEFL;
    int8_t l_10 = 1L;
    int32_t l_11 = 5L;
    int32_t l_51 = 0xF321248CL;
    int8_t l_62 = 0x07L;
    if (l_2)
    { 
        uint64_t l_23 = 18446744073709551611UL;
        int32_t l_35 = (-1L);
        if (g_3)
        { 
            int8_t l_9 = 0L;
            l_11 = (safe_mul_func_uint8_t_u_u((((l_8 ^= (safe_lshift_func_int16_t_s_u(l_2, 12))) , l_9) || g_3), l_10));
            for (l_2 = 0; (l_2 != (-27)); l_2 = safe_sub_func_int8_t_s_s(l_2, 3))
            { 
                --g_14;
            }
        }
        else
        { 
            int32_t l_19 = 0x4795ED7CL;
            if ((((safe_mul_func_int8_t_s_s((g_3 , 6L), l_19)) , g_3) >= 0x38L))
            { 
                --g_20;
                return l_23;
            }
            else
            { 
                int8_t l_28 = 0xFEL;
                int32_t l_29 = 0xEB2D3650L;
                g_27 &= (safe_div_func_int16_t_s_s((g_26 = 0x8FB8L), g_20));
                l_29 = (l_28 &= g_26);
            }
            for (g_26 = 0; (g_26 >= (-2)); g_26 = safe_sub_func_uint32_t_u_u(g_26, 6))
            { 
                uint32_t l_38 = 0UL;
                for (g_14 = (-4); (g_14 != 9); g_14++)
                { 
                    g_34 |= g_20;
                }
                l_35 ^= l_10;
                g_39 &= ((safe_mod_func_int8_t_s_s(((((g_34 > g_3) == l_38) == l_19) >= g_14), l_19)) <= g_26);
            }
            g_42 = ((((safe_mul_func_uint16_t_u_u(0x9E77L, (-10L))) == 0xEFL) != 0x8AL) ^ g_26);
            g_46 |= (g_45 = (safe_rshift_func_int16_t_s_u((-1L), g_39)));
        }
        l_35 &= ((safe_rshift_func_uint8_t_u_u((safe_mul_func_uint8_t_u_u(1UL, 3L)), l_51)) == 1L);
    }
    else
    { 
        int32_t l_60 = 0xD8BAC8E9L;
        l_51 |= (((safe_add_func_int32_t_s_s((safe_lshift_func_uint8_t_u_u((safe_mul_func_uint8_t_u_u((safe_add_func_int8_t_s_s(((l_8 = (g_61 = l_60)) <= 0x9665FEC6L), (-3L))), 0x39L)), g_42)), (-2L))) , l_62) & l_62);
        g_63 = l_62;
    }
    return l_62;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    transparent_crc(g_34, "g_34", print_hash_value);
    transparent_crc(g_39, "g_39", print_hash_value);
    transparent_crc(g_42, "g_42", print_hash_value);
    transparent_crc(g_45, "g_45", print_hash_value);
    transparent_crc(g_46, "g_46", print_hash_value);
    transparent_crc(g_61, "g_61", print_hash_value);
    transparent_crc(g_63, "g_63", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
