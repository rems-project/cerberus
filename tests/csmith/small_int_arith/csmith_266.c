// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_266.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 2L;
static uint32_t g_18 = 7UL;
static uint32_t g_19 = 0x4C6A37D7L;
static uint16_t g_27 = 65533UL;
static uint16_t g_28 = 8UL;
static int8_t g_30 = (-1L);
static uint64_t g_36 = 0x469F41AF53C8CBF6LL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int32_t l_12 = (-1L);
    int32_t l_29 = 0x298BBEB9L;
    for (g_2 = (-30); (g_2 > 8); ++g_2)
    { 
        uint32_t l_5 = 0x951AD386L;
        int16_t l_17 = 0x320FL;
        int32_t l_23 = 0L;
        if (l_5)
        { 
            for (l_5 = (-1); (l_5 <= 12); l_5 = safe_add_func_uint32_t_u_u(l_5, 5))
            { 
                l_12 |= (((safe_sub_func_uint32_t_u_u((safe_mod_func_int32_t_s_s(l_5, g_2)), 0x1FC9A57BL)) || g_2) <= 0xC4D1454BCD76CE4ALL);
                return g_2;
            }
        }
        else
        { 
            uint64_t l_26 = 1UL;
            g_19 = ((safe_add_func_uint64_t_u_u((g_18 = (safe_mul_func_uint16_t_u_u((((0L == 0xFA017779A7B445ACLL) , g_2) < g_2), l_17))), (-2L))) < l_5);
            for (l_5 = (-25); (l_5 <= 32); l_5++)
            { 
                uint16_t l_22 = 1UL;
                l_23 = (l_22 & g_19);
                g_27 = ((safe_lshift_func_uint16_t_u_s(g_2, l_26)) , (-1L));
                if ((0x5F19716E289AA508LL == l_26))
                { 
                    if (g_2)
                        break;
                }
                else
                { 
                    g_28 |= (l_5 <= l_17);
                }
            }
        }
        l_29 = 0x222C7E12L;
        g_30 &= (0L < 0x9E13C9534CE5FEF4LL);
    }
    for (l_12 = 0; (l_12 > 2); ++l_12)
    { 
        int32_t l_35 = 0xC0E84896L;
        int32_t l_41 = 1L;
        l_29 |= (l_35 = (safe_lshift_func_uint8_t_u_u((0xD39EF5B506946CB4LL ^ 18446744073709551615UL), 4)));
        g_36++;
        g_2 = (safe_div_func_int32_t_s_s(((249UL && l_29) , (-5L)), l_35));
        l_41 &= ((l_35 | g_28) > 0x2A1DL);
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
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    transparent_crc(g_36, "g_36", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
