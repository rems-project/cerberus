// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_158.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-1L);
static int32_t g_5 = 0L;
static int32_t g_17 = 1L;
static uint64_t g_22 = 0xCB5542AFA017779ALL;
static uint16_t g_27 = 0x7C71L;
static int32_t g_28 = 0L;
static uint8_t g_35 = 0x7EL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int16_t l_45 = (-1L);
    for (g_2 = 22; (g_2 < (-24)); g_2--)
    { 
        uint32_t l_38 = 0x9534CE5FL;
        for (g_5 = 25; (g_5 <= 12); g_5 = safe_sub_func_uint8_t_u_u(g_5, 7))
        { 
            uint16_t l_14 = 0x76B8L;
            int32_t l_34 = 0x7E12FD89L;
            if (((((safe_mod_func_int64_t_s_s(((safe_lshift_func_uint16_t_u_s((safe_sub_func_uint64_t_u_u(l_14, g_5)), 5)) <= l_14), g_5)) && 7UL) , g_2) , g_2))
            { 
                int16_t l_29 = 1L;
                for (l_14 = 0; (l_14 > 38); l_14++)
                { 
                    int32_t l_20 = 0x1EBF0DDDL;
                    int32_t l_21 = 0xFADACD7DL;
                    for (g_17 = (-5); (g_17 != 5); g_17 = safe_add_func_int32_t_s_s(g_17, 4))
                    { 
                        ++g_22;
                        g_28 = ((g_27 = ((safe_mod_func_int16_t_s_s(((g_17 <= l_14) || 0x4DDB84C6A37D7C86LL), 3L)) , (-6L))) < (-1L));
                    }
                    l_29 = ((g_27 == 1UL) ^ 0x09CA4F06702E6337LL);
                    l_34 ^= ((g_22 = (safe_div_func_uint16_t_u_u((safe_add_func_uint16_t_u_u(2UL, g_2)), g_27))) | 0xC786C7A88FF7673ELL);
                }
                g_35--;
            }
            else
            { 
                l_38 ^= (g_17 , g_27);
            }
            for (l_38 = 26; (l_38 == 48); l_38++)
            { 
                for (g_27 = (-18); (g_27 != 60); g_27 = safe_add_func_int64_t_s_s(g_27, 2))
                { 
                    l_34 = (g_17 <= 0xFD39EF5BL);
                    g_28 &= (safe_lshift_func_uint16_t_u_u(65534UL, 10));
                }
            }
            g_28 = (g_22 == g_27);
        }
        g_5 ^= l_45;
        for (g_17 = 0; (g_17 < 18); g_17++)
        { 
            g_28 = g_22;
        }
    }
    for (g_35 = 27; (g_35 != 11); g_35--)
    { 
        uint32_t l_62 = 0x31BC1F9CL;
        if (g_2)
        { 
            uint32_t l_57 = 1UL;
            int32_t l_60 = (-3L);
            for (g_17 = (-1); (g_17 != 15); g_17++)
            { 
                uint8_t l_52 = 0x38L;
                int32_t l_61 = 0x4B4FBF64L;
                ++l_52;
                for (g_5 = (-4); (g_5 != (-8)); g_5 = safe_sub_func_int16_t_s_s(g_5, 7))
                { 
                    l_57++;
                    if (g_28)
                        continue;
                }
                --l_62;
            }
        }
        else
        { 
            return l_45;
        }
    }
    return g_17;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
