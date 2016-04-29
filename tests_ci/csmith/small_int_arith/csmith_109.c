// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_109.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = (-1L);
static int64_t g_8 = 0x4006310FECAFE8B0LL;
static int16_t g_9 = 1L;
static int64_t g_11 = 1L;
static uint16_t g_16 = 0x5FBAL;
static uint16_t g_27 = 1UL;
static int64_t g_44 = 0x71B4D09D52FFABE4LL;
static uint64_t g_46 = 0xBFD6FFBBA6F2DB44LL;
static int64_t g_49 = (-6L);
static uint32_t g_51 = 4294967295UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int16_t l_2 = (-1L);
    int32_t l_10 = (-7L);
    uint16_t l_42 = 0xE4BCL;
    g_3 ^= (0x6BL > l_2);
    for (l_2 = (-26); (l_2 == (-7)); ++l_2)
    { 
        if (g_3)
            break;
    }
    g_11 = ((((((safe_mod_func_int16_t_s_s((l_10 |= (g_9 = (g_8 ^= g_3))), l_2)) >= g_3) , g_9) && g_8) == 0xE124L) & g_3);
    if (l_10)
    { 
        int64_t l_12 = 1L;
        int32_t l_15 = 9L;
        l_12 = (g_3 & g_8);
        l_10 = ((safe_mod_func_int8_t_s_s((((l_15 &= (g_9 != 0x0672L)) == g_3) == l_2), g_8)) && l_10);
        g_16--;
    }
    else
    { 
        int32_t l_24 = (-3L);
        int32_t l_35 = 0x2708CDB5L;
lbl_50:
        if ((((((l_10 | g_8) , l_2) < l_2) || g_9) ^ l_10))
        { 
            uint32_t l_19 = 0x5807C1ABL;
            int32_t l_20 = 1L;
            l_20 = (((g_9 == (-5L)) && l_19) , l_10);
        }
        else
        { 
            uint32_t l_23 = 8UL;
            l_24 ^= (safe_lshift_func_uint16_t_u_u(((g_9 & l_2) || l_23), g_8));
            g_27 = (safe_div_func_uint32_t_u_u((((l_10 || (-1L)) , l_10) != l_23), l_10));
        }
        l_35 = (safe_add_func_uint64_t_u_u((safe_sub_func_uint32_t_u_u((((safe_sub_func_int32_t_s_s((!0L), 4294967295UL)) , g_11) < (-2L)), 0x846E972FL)), l_2));
        if ((g_16 ^ 0x102D1F73L))
        { 
            uint32_t l_43 = 0xA2F90942L;
            l_35 ^= (safe_mul_func_uint16_t_u_u(g_27, 0x3530L));
            l_43 = ((safe_lshift_func_int8_t_s_u(((safe_mod_func_int64_t_s_s((g_9 <= 1UL), l_35)) > g_8), g_16)) != l_42);
            g_44 = ((g_16 & 0x2FA57A880E1B4ADCLL) != (-5L));
        }
        else
        { 
            uint16_t l_45 = 0xF9F8L;
            g_46 = (((l_45 = 0xA01DC0BFL) != g_9) && g_16);
            g_49 ^= ((safe_mod_func_uint64_t_u_u(g_27, 18446744073709551610UL)) , (-1L));
            if (g_16)
                goto lbl_50;
            g_51 = ((0x9E808E27L == l_35) > 0x98B2365BL);
        }
    }
    return g_44;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    transparent_crc(g_44, "g_44", print_hash_value);
    transparent_crc(g_46, "g_46", print_hash_value);
    transparent_crc(g_49, "g_49", print_hash_value);
    transparent_crc(g_51, "g_51", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
