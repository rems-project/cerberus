// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_133.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-4L);
static int32_t g_5 = (-1L);
static uint32_t g_9 = 0x0194DDBCL;
static int32_t g_30 = 0x2E5F58CDL;
static uint64_t g_31 = 0x679BDD86BDAE8940LL;
static uint16_t g_41 = 0xB95CL;
static int32_t g_45 = (-1L);
static int16_t g_50 = 0x6E0AL;
static uint32_t g_53 = 0UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_8 = 0xEE7D214CL;
    int32_t l_22 = (-7L);
    int8_t l_29 = (-7L);
    uint64_t l_34 = 18446744073709551615UL;
    int32_t l_42 = 0L;
    int32_t l_43 = 0x40778D40L;
    int32_t l_44 = 0xFF7828E9L;
    int32_t l_46 = 7L;
    int32_t l_47 = 0x18E8DCE9L;
    int32_t l_48 = 0xCE724D25L;
    int8_t l_49 = (-10L);
    int8_t l_51 = 0xAAL;
    int32_t l_52 = 0x7FC3FE76L;
    int8_t l_57 = (-2L);
    for (g_2 = 0; (g_2 != 3); g_2 = safe_add_func_uint64_t_u_u(g_2, 4))
    { 
        int32_t l_16 = (-1L);
        for (g_5 = 11; (g_5 <= (-14)); --g_5)
        { 
            g_9 = l_8;
        }
        for (l_8 = (-19); (l_8 < 37); l_8 = safe_add_func_uint64_t_u_u(l_8, 4))
        { 
            int32_t l_15 = (-1L);
            for (g_5 = 9; (g_5 < 11); g_5 = safe_add_func_uint16_t_u_u(g_5, 1))
            { 
                int32_t l_14 = 0xA831EB23L;
                l_15 = ((l_14 &= 0x6BA47C9D5FAC1226LL) < g_5);
                if (l_14)
                    goto lbl_56;
                if (((1L != l_16) & 0UL))
                { 
                    int32_t l_21 = 1L;
                    l_22 = ((((((safe_rshift_func_uint8_t_u_u(((safe_div_func_uint64_t_u_u(g_2, l_21)) , l_14), 7)) >= 0xC23EDB39L) | 0xD972L) | l_14) < l_14) | 1UL);
                }
                else
                { 
                    for (l_14 = (-12); (l_14 <= 28); l_14 = safe_add_func_int32_t_s_s(l_14, 3))
                    { 
                        g_31 = (g_30 ^= (safe_mod_func_int8_t_s_s((safe_mul_func_uint8_t_u_u(((g_5 , l_29) && l_14), 252UL)), 250UL)));
                    }
                    for (l_29 = 0; (l_29 < 7); ++l_29)
                    { 
                        uint32_t l_40 = 18446744073709551615UL;
                        l_34 = g_9;
                        l_15 = (safe_div_func_int16_t_s_s((+((safe_sub_func_uint32_t_u_u(g_2, g_9)) > 0UL)), l_40));
                        return l_14;
                    }
                    g_41 = (0x987C837EL == l_16);
                }
            }
            if (l_29)
                break;
            g_5 = l_15;
        }
        return g_41;
    }
lbl_56:
    ++g_53;
    return l_57;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    transparent_crc(g_41, "g_41", print_hash_value);
    transparent_crc(g_45, "g_45", print_hash_value);
    transparent_crc(g_50, "g_50", print_hash_value);
    transparent_crc(g_53, "g_53", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
