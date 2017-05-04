// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_322.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-1L);



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_5 = 4294967295UL;
    for (g_2 = 0; (g_2 <= (-11)); g_2 = safe_sub_func_uint16_t_u_u(g_2, 5))
    { 
        int8_t l_6 = (-1L);
        int32_t l_13 = 0L;
        uint8_t l_14 = 1UL;
        l_5 = (2L < g_2);
        l_6 ^= 9L;
        l_13 = (safe_lshift_func_uint16_t_u_u((safe_mul_func_int16_t_s_s(((safe_div_func_int8_t_s_s(g_2, g_2)) < 0x60F7L), l_6)), 8));
        l_14++;
    }
    return l_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
