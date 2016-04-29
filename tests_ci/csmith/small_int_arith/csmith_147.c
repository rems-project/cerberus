// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_147.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xAD313DD3L;
static uint16_t g_10 = 0x8353L;
static uint8_t g_11 = 0x0DL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint16_t l_7 = 0x90F1L;
    for (g_2 = 16; (g_2 > (-6)); g_2--)
    { 
        uint16_t l_8 = 1UL;
        if (g_2)
            break;
        l_8 = (safe_lshift_func_uint16_t_u_u(g_2, l_7));
        g_11 &= ((+(((((g_10 = (0xB24CE554L != g_2)) , 0L) ^ 0UL) ^ g_2) >= g_2)) && 0UL);
        return g_11;
    }
    g_2 = (g_10 , l_7);
    g_2 = (safe_div_func_int32_t_s_s(((safe_rshift_func_int8_t_s_s((safe_sub_func_int64_t_s_s((safe_lshift_func_int16_t_s_u(l_7, g_10)), g_11)), l_7)) & 4294967295UL), g_10));
    return g_10;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
