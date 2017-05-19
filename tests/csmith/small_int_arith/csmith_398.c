// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_398.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 0xBAC04EE7L;
static int64_t g_4 = 1L;
static uint32_t g_13 = 18446744073709551615UL;
static uint64_t g_20 = 0x972C40A98CEEF9A8LL;
static int32_t g_22 = 0L;
static int32_t g_43 = 0x035E948EL;
static int8_t g_44 = 0x07L;
static uint32_t g_45 = 0x7B6EB5C5L;
static int32_t g_52 = (-6L);



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int16_t l_2 = (-2L);
    uint64_t l_11 = 0xCB4E76AB2AEE5A98LL;
    int32_t l_12 = 0xAF72B572L;
    int32_t l_26 = 0xAE89405DL;
    g_4 = ((l_2 & l_2) >= g_3);
    for (g_4 = 0; (g_4 <= (-22)); g_4 = safe_sub_func_int8_t_s_s(g_4, 1))
    { 
        int32_t l_21 = 0L;
        uint64_t l_32 = 4UL;
        if ((l_2 <= 0x71867B8F5F499006LL))
        { 
            g_13 = (safe_sub_func_uint32_t_u_u((l_12 |= ((safe_sub_func_int32_t_s_s((l_11 < 0xA8B35EDAL), l_2)) <= l_2)), g_3));
            for (l_2 = 0; (l_2 != (-23)); l_2 = safe_sub_func_uint16_t_u_u(l_2, 1))
            { 
                int32_t l_25 = (-4L);
                if (((safe_add_func_int64_t_s_s(g_4, (-1L))) > g_4))
                { 
                    for (g_13 = 20; (g_13 >= 39); g_13 = safe_add_func_uint64_t_u_u(g_13, 6))
                    { 
                        g_20 = g_3;
                    }
                }
                else
                { 
                    l_21 = 0x26595AD3L;
                    g_22 = (g_13 >= g_20);
                }
                g_22 = ((safe_mod_func_int8_t_s_s((l_26 = ((0x2FA5D8720725FC1CLL & l_25) & 0xE5F58CDC14C38D67LL)), g_3)) < l_25);
                l_21 = ((g_13 != l_2) & g_20);
                if (g_22)
                    continue;
            }
        }
        else
        { 
            uint32_t l_31 = 1UL;
            l_12 |= ((safe_add_func_uint16_t_u_u(((safe_add_func_int64_t_s_s(((0x11L != l_31) != g_3), l_26)) > g_13), l_26)) != 0xA8ACL);
            if (l_31)
                continue;
            l_32 = g_20;
        }
        for (l_32 = (-1); (l_32 < 42); l_32 = safe_add_func_uint32_t_u_u(l_32, 5))
        { 
            int32_t l_35 = 0x72CE3C48L;
            int32_t l_36 = 0x1FC5BFF9L;
            l_21 |= (g_22 ^= l_35);
            l_36 = (((-1L) == g_20) & l_21);
        }
        for (g_20 = 0; (g_20 == 9); g_20 = safe_add_func_int32_t_s_s(g_20, 1))
        { 
            uint32_t l_39 = 4294967295UL;
            int32_t l_42 = (-10L);
            l_39++;
            g_45--;
            g_43 = 4L;
        }
        for (g_3 = 0; (g_3 < 19); g_3 = safe_add_func_int16_t_s_s(g_3, 4))
        { 
            l_21 = (l_2 || 0L);
            return g_22;
        }
    }
    g_43 = ((safe_mul_func_uint8_t_u_u(((g_22 = (l_12 |= g_44)) & l_2), g_52)) >= 1L);
    return g_13;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_43, "g_43", print_hash_value);
    transparent_crc(g_44, "g_44", print_hash_value);
    transparent_crc(g_45, "g_45", print_hash_value);
    transparent_crc(g_52, "g_52", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
