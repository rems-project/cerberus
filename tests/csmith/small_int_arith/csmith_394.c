// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_394.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = (-1L);
static int32_t g_12 = 0xA278C007L;
static int8_t g_18 = 0x64L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_2 = 0x5DCEC3D7D490C4D8LL;
    int32_t l_26 = 0x532D49ACL;
    if ((l_2 , g_3))
    { 
        int64_t l_11 = 0x3498E64E6DC660F7LL;
        int32_t l_17 = 0xEB2FC257L;
        int32_t l_23 = 0L;
        for (l_2 = (-30); (l_2 > 16); l_2 = safe_add_func_int16_t_s_s(l_2, 1))
        { 
            int16_t l_6 = 0x11C1L;
            int32_t l_20 = 0xE01E6E83L;
            if (l_6)
                break;
            if ((g_12 = (safe_mul_func_int16_t_s_s(((safe_rshift_func_uint8_t_u_s((l_11 , 0x47L), g_3)) && 3UL), g_3))))
            { 
                g_18 |= (l_17 = (((safe_lshift_func_int16_t_s_u((safe_add_func_int16_t_s_s(0L, g_12)), 5)) >= g_12) == g_3));
            }
            else
            { 
                int64_t l_19 = 0x4939E63A5BED8572LL;
                l_20 = ((((((g_18 = ((g_18 >= l_19) ^ 0xEDL)) , l_6) , 7UL) == l_2) , g_18) | 0x25L);
            }
        }
        for (l_17 = 0; (l_17 >= 2); ++l_17)
        { 
            l_23 = g_3;
            return g_18;
        }
    }
    else
    { 
        l_26 ^= (safe_mod_func_uint64_t_u_u(18446744073709551613UL, 18446744073709551615UL));
    }
    return l_26;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
