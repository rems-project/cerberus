// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_355.c
#include "csmith.h"


static long __undefined;



static int8_t g_10 = 0xE4L;
static int32_t g_11 = (-1L);
static uint16_t g_12 = 0x5931L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint8_t l_9 = 0UL;
    if ((safe_unary_minus_func_int32_t_s(((safe_mul_func_int16_t_s_s((((safe_rshift_func_uint16_t_u_s(((safe_div_func_uint8_t_u_u(l_9, g_10)) > l_9), g_10)) ^ l_9) >= g_10), l_9)) <= 2L))))
    { 
        uint32_t l_13 = 0x662DB8E9L;
        l_13 &= (g_12 = (g_11 = l_9));
    }
    else
    { 
        return g_10;
    }
    g_11 = g_12;
    return g_11;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
