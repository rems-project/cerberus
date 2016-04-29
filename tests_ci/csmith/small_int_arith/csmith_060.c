// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_060.c
#include "csmith.h"


static long __undefined;



static uint32_t g_5 = 1UL;
static int32_t g_11 = 0L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint8_t l_2 = 0xB1L;
    int32_t l_10 = (-1L);
    l_2 ^= 0x399841B3L;
    g_5 = (safe_mod_func_uint16_t_u_u(l_2, (-4L)));
    if ((safe_mul_func_int8_t_s_s(((4294967287UL <= g_5) > 0L), l_10)))
    { 
        uint16_t l_12 = 0xD065L;
        int32_t l_15 = 0x79B69B2EL;
        uint32_t l_16 = 0x34688073L;
        l_12 |= (g_11 |= 0x2579253AL);
        for (l_2 = 7; (l_2 >= 23); l_2 = safe_add_func_uint16_t_u_u(l_2, 8))
        { 
            --l_16;
            if (l_10)
                break;
        }
        l_15 = (safe_lshift_func_int16_t_s_s(((((safe_rshift_func_uint16_t_u_s(l_15, g_5)) & l_2) != l_15) == 4294967295UL), g_5));
    }
    else
    { 
        return g_5;
    }
    return l_10;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
