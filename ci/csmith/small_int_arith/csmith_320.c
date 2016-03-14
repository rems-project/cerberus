// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_320.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 0x1897A4A1L;
static int8_t g_6 = 0xACL;
static int32_t g_12 = 0x050678E0L;
static int64_t g_13 = 0x3BC1B0FE2CF45657LL;
static int32_t g_14 = 0xA6E8F591L;
static int64_t g_15 = (-8L);
static int8_t g_31 = 1L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int32_t l_2 = 0L;
    int32_t l_16 = 0L;
    int32_t l_18 = (-7L);
    uint16_t l_19 = 5UL;
    g_3 = l_2;
    l_2 = (safe_add_func_int8_t_s_s(g_3, g_3));
    g_6 &= l_2;
    if (((0L && 18446744073709551611UL) | 0xD0L))
    { 
        uint64_t l_11 = 0x06C0E2632C5B641BLL;
        int32_t l_17 = 0xFE0CD1B7L;
        for (g_6 = 0; (g_6 >= 16); ++g_6)
        { 
            g_12 &= ((((((safe_lshift_func_int8_t_s_u(g_6, 6)) && l_2) & g_6) && 0x0D3ECF04B064BAE0LL) < l_11) == g_6);
        }
        ++l_19;
        g_14 = (l_16 ^= ((((safe_unary_minus_func_int64_t_s((l_11 == g_6))) , g_12) >= g_12) || l_11));
    }
    else
    { 
        uint32_t l_23 = 1UL;
        int32_t l_33 = 2L;
        if (l_23)
        { 
            uint64_t l_32 = 0x3D2C82F3C076A5D0LL;
            g_31 |= ((((safe_add_func_int32_t_s_s(((safe_mul_func_int16_t_s_s((safe_lshift_func_int16_t_s_u(((((!g_12) || g_14) , l_18) , g_3), 15)), g_3)) != 0x00L), g_6)) | l_23) & l_18) ^ l_18);
            l_33 |= ((0x4575F7F7L & l_32) , (-1L));
        }
        else
        { 
            int8_t l_41 = 0x16L;
            g_12 |= ((safe_lshift_func_int8_t_s_u((((safe_sub_func_int32_t_s_s((safe_sub_func_int64_t_s_s((safe_unary_minus_func_uint64_t_u(6UL)), l_23)), g_15)) || g_15) == l_41), 0)) < 4UL);
        }
    }
    return g_14;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
