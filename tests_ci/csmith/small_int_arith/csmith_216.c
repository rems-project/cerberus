// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_216.c
#include "csmith.h"


static long __undefined;



static int16_t g_12 = 0L;
static int32_t g_22 = (-2L);
static int16_t g_31 = 4L;
static int32_t g_42 = 0x6F739807L;
static int64_t g_43 = 8L;
static uint32_t g_45 = 0x10F1939EL;
static int8_t g_47 = 0L;
static int32_t g_49 = (-1L);
static uint64_t g_50 = 0x64A3A207B8A5F036LL;
static uint64_t g_59 = 0xEF3BB579AB67338DLL;
static int32_t g_64 = (-6L);



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint32_t l_10 = 4294967295UL;
    int16_t l_11 = 0xA924L;
    int32_t l_30 = 8L;
    int32_t l_32 = 0L;
    int32_t l_67 = 0x79D795BCL;
lbl_48:
    if (((safe_mul_func_uint8_t_u_u(((safe_sub_func_uint64_t_u_u((safe_lshift_func_int8_t_s_s(((safe_sub_func_int64_t_s_s((l_10 < l_11), g_12)) , 1L), 6)), 0UL)) | l_10), g_12)) <= 0xF14EB4C8F0D0714ALL))
    { 
        uint64_t l_15 = 0xFEBFB2C41AC3DC99LL;
        int32_t l_26 = (-7L);
        l_15 |= (safe_div_func_uint16_t_u_u(((4294967290UL ^ g_12) || g_12), (-3L)));
        for (l_15 = 0; (l_15 < 38); l_15 = safe_add_func_uint64_t_u_u(l_15, 9))
        { 
            for (l_10 = 1; (l_10 <= 34); l_10++)
            { 
                return l_15;
            }
            g_22 = (safe_add_func_int32_t_s_s(0xC9B996A5L, l_11));
            for (g_12 = (-11); (g_12 < (-5)); g_12 = safe_add_func_uint16_t_u_u(g_12, 8))
            { 
                uint64_t l_25 = 0xAA08BBD188380095LL;
                int32_t l_29 = 1L;
                l_26 &= ((0x13C27F35L != l_25) | 0L);
                for (l_10 = 0; (l_10 != 48); l_10 = safe_add_func_int16_t_s_s(l_10, 6))
                { 
                    l_30 = (l_29 = l_10);
                }
            }
        }
    }
    else
    { 
        uint32_t l_44 = 18446744073709551612UL;
        l_32 ^= ((l_30 = ((((g_31 = g_12) == 1UL) & g_22) < 0x17B4D2C298C245E3LL)) != 0L);
        if ((g_22 ^ g_22))
        { 
            int32_t l_41 = 1L;
            g_43 = ((safe_lshift_func_uint16_t_u_u(((safe_mod_func_uint16_t_u_u((g_42 = (safe_sub_func_int64_t_s_s((safe_unary_minus_func_uint8_t_u(((safe_unary_minus_func_int8_t_s(g_12)) || l_11))), l_41))), 0xB270L)) && 0xC77E2192L), 14)) , 0x8D911ACAL);
            return l_44;
        }
        else
        { 
            l_32 = 8L;
            g_45 = l_11;
        }
    }
    if ((g_47 = ((!g_12) || l_11)))
    { 
        if (g_22)
            goto lbl_48;
        --g_50;
    }
    else
    { 
        int16_t l_58 = 1L;
        for (g_45 = 0; (g_45 > 5); g_45 = safe_add_func_int16_t_s_s(g_45, 6))
        { 
            int32_t l_57 = 1L;
            l_58 ^= (safe_div_func_uint32_t_u_u((9L ^ 7L), l_57));
            g_59--;
        }
        g_64 |= (safe_mul_func_uint8_t_u_u(g_12, l_10));
        l_67 |= (safe_mod_func_uint16_t_u_u((g_42 < 1L), 0x000BL));
    }
    return l_30;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    transparent_crc(g_42, "g_42", print_hash_value);
    transparent_crc(g_43, "g_43", print_hash_value);
    transparent_crc(g_45, "g_45", print_hash_value);
    transparent_crc(g_47, "g_47", print_hash_value);
    transparent_crc(g_49, "g_49", print_hash_value);
    transparent_crc(g_50, "g_50", print_hash_value);
    transparent_crc(g_59, "g_59", print_hash_value);
    transparent_crc(g_64, "g_64", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
