// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_323.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x71177E8EL;
static int8_t g_28 = (-9L);
static uint32_t g_38 = 8UL;
static uint64_t g_39 = 1UL;
static int16_t g_40 = (-5L);
static uint32_t g_52 = 0xE52129E5L;
static uint32_t g_60 = 9UL;
static uint8_t g_64 = 7UL;
static int32_t g_65 = 0L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint16_t l_27 = 0x0549L;
    int16_t l_41 = 0L;
    int32_t l_50 = 0x4EA65D33L;
    for (g_2 = 29; (g_2 <= (-29)); g_2 = safe_sub_func_uint64_t_u_u(g_2, 3))
    { 
        uint32_t l_5 = 0xE923E64FL;
        int32_t l_6 = 0L;
        int32_t l_7 = 0xCED8F6EFL;
        uint32_t l_55 = 0xF2A6BC67L;
        l_7 = ((l_6 = (g_2 <= l_5)) ^ 2L);
        if (((safe_add_func_uint16_t_u_u(((safe_lshift_func_uint16_t_u_s((~((safe_div_func_uint8_t_u_u((safe_div_func_int16_t_s_s((((safe_div_func_int16_t_s_s((((g_28 = (safe_rshift_func_int16_t_s_s((safe_lshift_func_int8_t_s_u((safe_sub_func_int16_t_s_s((((-1L) > l_27) | l_27), 1UL)), g_2)), l_7))) , 0x8A01L) && 0x08AFL), 0x6B7AL)) < 0x6C8951BBL) > l_27), g_2)), l_5)) < 0L)), 7)) | 65526UL), 1L)) || 0xC8L))
        { 
            uint16_t l_31 = 65533UL;
            int32_t l_37 = 0L;
            for (l_5 = 0; (l_5 == 15); l_5 = safe_add_func_int8_t_s_s(l_5, 1))
            { 
                int32_t l_36 = (-1L);
                l_31 = g_2;
                g_38 = (safe_div_func_int32_t_s_s((((safe_lshift_func_int8_t_s_s((l_37 = (l_36 ^ g_28)), 2)) > 1L) >= g_28), g_2));
                g_39 = 0x205E60D1L;
            }
        }
        else
        { 
            uint32_t l_42 = 1UL;
            int32_t l_51 = 1L;
            --l_42;
            l_6 = (((safe_lshift_func_int16_t_s_s(l_42, g_2)) != 0xE745L) == 255UL);
            for (l_41 = 0; (l_41 > (-6)); l_41--)
            { 
                int16_t l_49 = 0xB576L;
                int32_t l_58 = (-4L);
                int32_t l_59 = (-10L);
                if ((g_28 | l_49))
                { 
                    g_52++;
                }
                else
                { 
                    uint32_t l_63 = 0x149088B5L;
                    ++l_55;
                    if ((g_38 < l_7))
                    { 
                        if (g_52)
                            break;
                        if (l_5)
                            break;
                        g_60--;
                    }
                    else
                    { 
                        return l_63;
                    }
                    g_64 = (-10L);
                }
            }
        }
        g_65 = g_52;
    }
    g_2 = 0L;
    for (g_40 = 0; (g_40 == 16); ++g_40)
    { 
        l_50 |= ((safe_sub_func_uint32_t_u_u((0x38L < g_60), l_41)) , g_28);
    }
    return g_65;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    transparent_crc(g_39, "g_39", print_hash_value);
    transparent_crc(g_40, "g_40", print_hash_value);
    transparent_crc(g_52, "g_52", print_hash_value);
    transparent_crc(g_60, "g_60", print_hash_value);
    transparent_crc(g_64, "g_64", print_hash_value);
    transparent_crc(g_65, "g_65", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
