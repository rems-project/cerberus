// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_120.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 0x6DE7L;
static int32_t g_3 = 0x3EB905D0L;
static int32_t g_12 = 0L;
static uint8_t g_31 = 0x18L;
static int32_t g_34 = 1L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int16_t l_10 = 0x6A07L;
    uint8_t l_23 = 1UL;
    uint64_t l_24 = 0xE9973063D62A04F7LL;
    int8_t l_32 = (-1L);
    int32_t l_39 = 0x5678D568L;
    g_3 &= ((-2L) >= g_2);
    g_3 = g_3;
    for (g_2 = 1; (g_2 >= 39); ++g_2)
    { 
        uint32_t l_11 = 0x7182B474L;
        g_3 ^= (safe_add_func_uint16_t_u_u(0x7BF4L, (-1L)));
        for (g_3 = 0; (g_3 <= 8); g_3++)
        { 
            int8_t l_13 = (-3L);
            g_12 = ((l_10 , l_11) > g_3);
            return l_13;
        }
    }
    if ((!(safe_sub_func_uint16_t_u_u((safe_add_func_uint16_t_u_u((safe_mul_func_uint8_t_u_u(((((safe_rshift_func_uint8_t_u_u((l_10 ^ 4UL), l_23)) && l_23) != l_23) < 0x30L), l_23)), l_24)), l_23))))
    { 
        uint32_t l_33 = 0xDE30ECA6L;
        g_34 |= ((((safe_mod_func_uint16_t_u_u((((safe_sub_func_int64_t_s_s((safe_sub_func_int16_t_s_s((g_31 = g_3), 0x6A1CL)), l_32)) || 0UL) , g_31), l_33)) <= 18446744073709551615UL) ^ 252UL) < l_10);
    }
    else
    { 
        int16_t l_37 = 8L;
        int32_t l_38 = 0x7CB0BE94L;
        l_39 = (((safe_div_func_int16_t_s_s(((g_3 <= l_37) < g_12), 65534UL)) && g_12) | l_38);
        g_3 |= (safe_lshift_func_int16_t_s_s((safe_add_func_int64_t_s_s(l_38, 8UL)), 9));
    }
    return g_12;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    transparent_crc(g_34, "g_34", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
