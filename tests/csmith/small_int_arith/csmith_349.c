// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_349.c
#include "csmith.h"


static long __undefined;



static uint32_t g_6 = 0x4288A137L;
static int32_t g_10 = 5L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint64_t l_7 = 0x836CCB03629AA810LL;
    int32_t l_8 = (-1L);
    l_8 ^= ((safe_add_func_uint8_t_u_u((safe_div_func_uint32_t_u_u(0x125D16DFL, g_6)), l_7)) , g_6);
    g_10 |= ((((safe_unary_minus_func_int8_t_s(0x13L)) && g_6) ^ g_6) != 6L);
    return l_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
