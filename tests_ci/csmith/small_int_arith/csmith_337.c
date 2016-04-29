// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_337.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x110C93B4L;
static int32_t g_5 = 8L;
static uint32_t g_34 = 6UL;
static uint8_t g_35 = 0x43L;
static int8_t g_39 = (-1L);
static int64_t g_40 = 1L;
static uint32_t g_41 = 0x4A08DEB2L;
static uint16_t g_44 = 6UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint64_t l_10 = 0x672CA3C0BF90A233LL;
    int32_t l_19 = 0L;
    int32_t l_24 = 6L;
    int8_t l_25 = 0x0AL;
    for (g_2 = 0; (g_2 == (-5)); g_2 = safe_sub_func_uint8_t_u_u(g_2, 2))
    { 
        uint16_t l_17 = 65533UL;
        int32_t l_18 = 0x08FB0B44L;
        for (g_5 = 19; (g_5 != 18); g_5 = safe_sub_func_uint64_t_u_u(g_5, 2))
        { 
            int8_t l_8 = 5L;
            int32_t l_9 = 8L;
            if (l_8)
                break;
            if (g_2)
                continue;
            l_9 = (((l_10--) , ((l_19 = ((l_18 = (safe_lshift_func_uint8_t_u_s((safe_rshift_func_uint16_t_u_u((0xD2D9L ^ l_17), l_10)), 1))) & g_5)) & l_10)) || g_5);
        }
        g_5 &= 0x405CEFD0L;
        l_24 = (l_19 = (safe_lshift_func_int8_t_s_s(((safe_lshift_func_int8_t_s_s(g_5, 2)) & l_10), g_5)));
    }
    l_24 ^= ((g_2 <= l_25) | 0x35984225189D9E62LL);
    for (l_25 = 2; (l_25 == 24); ++l_25)
    { 
        uint8_t l_38 = 0xB1L;
        l_24 = g_2;
        for (g_5 = 29; (g_5 <= 18); --g_5)
        { 
            for (l_24 = 0; (l_24 == (-25)); l_24--)
            { 
                for (l_19 = (-6); (l_19 <= 24); l_19 = safe_add_func_uint64_t_u_u(l_19, 1))
                { 
                    g_34 |= g_2;
                    if (g_2)
                        break;
                    ++g_35;
                }
                if (g_5)
                    break;
            }
            g_39 ^= (g_2 < l_38);
            --g_41;
            g_44 = g_41;
        }
    }
    return g_35;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_34, "g_34", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    transparent_crc(g_39, "g_39", print_hash_value);
    transparent_crc(g_40, "g_40", print_hash_value);
    transparent_crc(g_41, "g_41", print_hash_value);
    transparent_crc(g_44, "g_44", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
