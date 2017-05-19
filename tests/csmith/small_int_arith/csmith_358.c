// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_358.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2 = 0x5C96DD1E1E87DF2FLL;
static uint32_t g_20 = 0x52E4A6B2L;
static int8_t g_22 = 0x3EL;
static uint32_t g_35 = 4294967295UL;
static int32_t g_41 = 1L;
static int8_t g_42 = (-1L);
static uint64_t g_49 = 0xB058B506EE4F120BLL;
static int32_t g_56 = (-3L);
static uint32_t g_57 = 1UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int16_t l_3 = 0x8F82L;
    int32_t l_10 = 0x537C57F3L;
    int32_t l_33 = (-2L);
    l_3 = g_2;
    if ((safe_div_func_uint16_t_u_u((((((((l_3 <= (-1L)) , g_2) || l_3) & l_3) != l_3) < g_2) || l_3), g_2)))
    { 
        int16_t l_8 = (-9L);
        l_8 = (safe_unary_minus_func_int32_t_s(((~0L) , 1L)));
    }
    else
    { 
        int16_t l_9 = 7L;
        int32_t l_47 = 0L;
        l_9 = l_3;
        if (g_2)
            goto lbl_11;
lbl_11:
        l_10 = ((((g_2 || 0xBE360DE5L) , l_9) > 0xEBBD4856CD833989LL) , g_2);
        for (l_10 = 0; (l_10 > (-4)); l_10--)
        { 
            uint16_t l_23 = 0x6F63L;
            for (l_3 = 0; (l_3 >= 17); ++l_3)
            { 
                uint32_t l_21 = 4294967290UL;
                int32_t l_34 = 0x3964E48CL;
                for (l_9 = 0; (l_9 == 26); l_9++)
                { 
                    int64_t l_27 = 0xDAD4F6C5533F2A6ALL;
                    for (g_2 = 10; (g_2 == 25); g_2 = safe_add_func_uint64_t_u_u(g_2, 9))
                    { 
                        uint64_t l_26 = 18446744073709551615UL;
                        int32_t l_28 = 0x938140A9L;
                        g_20 |= g_2;
                        g_22 = ((l_21 & g_20) , g_2);
                        if (l_23)
                            break;
                        l_28 = (((safe_mul_func_uint16_t_u_u(l_26, 0L)) && l_27) , g_2);
                    }
                    l_33 = (safe_sub_func_uint16_t_u_u((safe_mul_func_uint8_t_u_u((0x9D95921BA52B3395LL >= g_20), g_20)), g_2));
                }
                l_34 = g_20;
                --g_35;
                for (g_20 = 0; (g_20 <= 46); g_20++)
                { 
                    uint16_t l_54 = 0xE1D8L;
                    int32_t l_55 = 0xF1A9F139L;
                    l_33 = (g_42 = ((g_41 = (~g_20)) <= g_20));
                    for (g_2 = 13; (g_2 != 48); g_2 = safe_add_func_uint32_t_u_u(g_2, 1))
                    { 
                        l_47 ^= (safe_lshift_func_int16_t_s_u((l_9 , 0x0AC8L), l_34));
                        g_49 &= (!(((((g_42 & g_41) , l_33) && g_35) , 0x65BBL) & 1L));
                        l_55 &= ((safe_lshift_func_uint8_t_u_u(((safe_lshift_func_int16_t_s_u(g_2, l_3)) >= l_54), 6)) | g_42);
                        g_57++;
                    }
                    l_55 |= ((((0x39C3L != l_23) , 0x68FBL) , g_56) >= g_57);
                }
            }
            g_41 |= l_9;
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
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    transparent_crc(g_41, "g_41", print_hash_value);
    transparent_crc(g_42, "g_42", print_hash_value);
    transparent_crc(g_49, "g_49", print_hash_value);
    transparent_crc(g_56, "g_56", print_hash_value);
    transparent_crc(g_57, "g_57", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
