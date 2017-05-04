// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_336.c
#include "csmith.h"


static long __undefined;



static int32_t g_8 = 0xB1A9565EL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int32_t l_7 = (-3L);
    int32_t l_9 = (-9L);
    l_9 |= ((safe_lshift_func_int16_t_s_u((safe_unary_minus_func_int32_t_s((((safe_rshift_func_int16_t_s_s(0xB618L, 14)) < l_7) | g_8))), g_8)) & l_7);
    return g_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
