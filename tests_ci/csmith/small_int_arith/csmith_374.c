// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_374.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 0x928CL;
static uint16_t g_5 = 65531UL;
static int32_t g_11 = 0x921E124DL;
static int32_t g_12 = 0x5466BC65L;
static int32_t g_17 = 7L;
static uint32_t g_30 = 0xB4763523L;
static int32_t g_31 = 9L;
static int32_t g_32 = 0xAA9D707DL;
static int8_t g_33 = 0L;
static int32_t g_46 = 0xBD68E480L;
static uint32_t g_47 = 4294967295UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint64_t l_10 = 0x7D50F82BAEF6E229LL;
    int32_t l_28 = 7L;
    int32_t l_36 = 0x8D3FD905L;
    uint8_t l_37 = 0x6AL;
lbl_18:
    ++g_2;
lbl_8:
    g_5 |= (0UL & 0xC3099CFEL);
    for (g_5 = 10; (g_5 == 57); ++g_5)
    { 
        int32_t l_9 = 0x0D193E05L;
        int32_t l_35 = 0x6DCB0C7BL;
        if (g_2)
            goto lbl_8;
        g_12 = ((g_11 = ((((l_9 = (-8L)) > 0x27L) < l_10) <= l_10)) >= g_2);
        if (g_12)
            continue;
        if ((safe_sub_func_uint16_t_u_u(((g_2 &= (g_12 | l_9)) != g_12), g_11)))
        { 
            uint32_t l_25 = 0xB64B6930L;
            uint32_t l_26 = 0x9C010580L;
            int32_t l_27 = 0x1F199E1FL;
            int32_t l_34 = 0x87C2657AL;
            for (g_12 = 3; (g_12 >= (-8)); --g_12)
            { 
                if (((l_10 ^ 0x7D96711DB6084EDCLL) & l_9))
                { 
                    g_17 = (l_10 , g_5);
                    if (l_9)
                        goto lbl_18;
                    l_28 = (safe_add_func_uint16_t_u_u((safe_add_func_int64_t_s_s((l_27 = (((((safe_mod_func_int32_t_s_s(0x314B8123L, l_25)) < l_26) , l_10) < g_17) > (-1L))), l_10)), 0xC6F0L));
                }
                else
                { 
                    int32_t l_29 = (-1L);
                    g_30 &= l_29;
                }
            }
            l_37++;
            l_35 &= (safe_lshift_func_uint16_t_u_s((g_33 , 7UL), 14));
        }
        else
        { 
            int32_t l_49 = 0x6E3B61EAL;
            for (g_2 = 5; (g_2 != 53); ++g_2)
            { 
                uint32_t l_48 = 0x075D7B1EL;
                g_31 &= (l_49 = ((((safe_mul_func_uint8_t_u_u(((((((((g_47 = ((g_46 && 0xDEBF624E194E4064LL) , g_2)) <= l_48) <= l_49) < 1L) && l_49) != 0xC5A97588L) ^ (-1L)) < l_35), 5UL)) != 8UL) | l_49) , l_9));
                return l_36;
            }
            if (g_12)
            { 
                uint32_t l_50 = 0x3A2AD41DL;
                l_50--;
            }
            else
            { 
                l_49 = ((~((safe_div_func_int16_t_s_s((((((safe_unary_minus_func_uint32_t_u(0xAEE1D35EL)) > g_17) , g_47) | l_35) , 8L), g_47)) == g_33)) >= g_30);
            }
        }
    }
    l_36 = ((((g_12 && 0xA741179D740F48B4LL) || (-5L)) >= g_46) == 1L);
    return g_30;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    transparent_crc(g_32, "g_32", print_hash_value);
    transparent_crc(g_33, "g_33", print_hash_value);
    transparent_crc(g_46, "g_46", print_hash_value);
    transparent_crc(g_47, "g_47", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
