// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_047.c
#include "csmith.h"


static long __undefined;



static uint8_t g_6 = 0x80L;
static uint8_t g_7 = 0x2BL;
static uint32_t g_21 = 0UL;
static int16_t g_23 = 1L;
static int32_t g_24 = 8L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int16_t l_8 = 6L;
    int32_t l_22 = 1L;
    l_8 = (safe_div_func_int32_t_s_s(((safe_sub_func_int64_t_s_s((g_6 = 0xA8B108F8256A9EF7LL), g_7)) != 0x5121L), 0x4888999DL));
    if ((safe_div_func_int64_t_s_s(l_8, l_8)))
    { 
        int16_t l_11 = 0xC285L;
        return l_11;
    }
    else
    { 
        for (g_6 = 13; (g_6 != 44); g_6++)
        { 
            int16_t l_20 = 4L;
            g_24 = ((safe_sub_func_uint16_t_u_u(((g_23 = (l_22 ^= (safe_mod_func_uint16_t_u_u(((g_21 ^= ((safe_sub_func_int32_t_s_s((((((0x74L >= g_7) > l_20) == g_7) , 0x0DE57413L) > l_20), g_6)) , g_7)) > l_20), 65531UL)))) , l_8), 9L)) & 0x900BL);
            if (l_20)
                continue;
        }
    }
    return l_22;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
