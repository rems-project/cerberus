// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_238.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 0x6BACD795L;
static int32_t g_4 = (-4L);
static int32_t g_9 = 0x141E4F1FL;
static int8_t g_10 = (-1L);
static int32_t g_11 = 0xF97812A3L;
static uint32_t g_12 = 0x21E1D82CL;
static uint32_t g_23 = 0xB622B607L;
static uint32_t g_29 = 0x783312EFL;
static uint32_t g_36 = 18446744073709551615UL;
static uint64_t g_51 = 0x08F18E0DA53D1EDBLL;
static int64_t g_58 = 0L;
static uint16_t g_61 = 3UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int16_t l_5 = 5L;
    int32_t l_8 = 0xE08A1101L;
    uint32_t l_32 = 4294967293UL;
    int32_t l_35 = 2L;
    int32_t l_39 = 0x2F2AA787L;
    uint32_t l_43 = 0x42F53403L;
    uint16_t l_69 = 65535UL;
    if ((((g_4 = (!g_3)) | l_5) || 1L))
    { 
lbl_73:
        g_10 = (g_9 = (l_8 = (g_3 = (safe_lshift_func_int8_t_s_s((g_3 == 1UL), 2)))));
        g_12++;
    }
    else
    { 
        int32_t l_22 = (-1L);
        int32_t l_44 = 0x2C199447L;
        g_9 |= (safe_mul_func_int8_t_s_s((safe_rshift_func_uint8_t_u_u(((+(l_8 |= ((((safe_mod_func_int64_t_s_s((0x43L & 0x80L), g_11)) == l_22) ^ 0x0278L) > l_22))) , g_4), 3)), g_4));
        g_23--;
        if ((l_8 , g_11))
        { 
            int16_t l_42 = (-1L);
            uint8_t l_60 = 0xFFL;
            g_3 = (safe_lshift_func_int8_t_s_s((l_8 >= g_9), g_4));
            if ((!1UL))
            { 
                --g_29;
                return l_8;
            }
            else
            { 
                l_32 = g_3;
                l_35 ^= ((safe_div_func_int16_t_s_s(g_4, l_8)) & l_5);
                g_36--;
                g_9 = (g_3 = l_39);
            }
            for (l_22 = 0; (l_22 > 3); l_22++)
            { 
                int32_t l_49 = 0L;
                int32_t l_59 = 0xC551464EL;
                g_9 = l_8;
                if (l_42)
                { 
                    int8_t l_50 = 0x14L;
                    l_44 = (l_43 , g_12);
                    if ((g_9 = (0xDFE8E23095C3C62ELL >= g_36)))
                    { 
                        int8_t l_47 = 0x37L;
                        int32_t l_48 = 0xAB2DD2C9L;
                        l_48 = (+(!(l_47 < g_23)));
                        l_49 = l_42;
                        ++g_51;
                    }
                    else
                    { 
                        g_9 = (safe_sub_func_int16_t_s_s((safe_sub_func_int8_t_s_s(l_39, 4UL)), l_50));
                        l_44 |= (g_10 , g_11);
                        l_59 = g_58;
                        l_60 = (g_4 && 0xB5077743L);
                    }
                }
                else
                { 
                    g_3 = l_49;
                }
                g_61++;
                if (l_44)
                    break;
            }
            l_22 = g_11;
        }
        else
        { 
            int16_t l_68 = 0L;
            int32_t l_70 = 0x0F7348F3L;
            l_70 = (((g_10 &= ((safe_mod_func_int64_t_s_s((((safe_mul_func_uint8_t_u_u((l_68 & g_12), g_11)) , 0x04A3L) , g_3), 1UL)) , (-3L))) & l_69) < g_12);
        }
        l_39 &= (safe_lshift_func_uint8_t_u_u(0xD0L, l_22));
    }
    if (g_11)
        goto lbl_73;
    l_39 ^= (g_3 &= (l_8 < g_23));
    return l_35;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_29, "g_29", print_hash_value);
    transparent_crc(g_36, "g_36", print_hash_value);
    transparent_crc(g_51, "g_51", print_hash_value);
    transparent_crc(g_58, "g_58", print_hash_value);
    transparent_crc(g_61, "g_61", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
