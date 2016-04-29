// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_063.c
#include "csmith.h"


static long __undefined;



static int16_t g_6 = (-4L);
static uint32_t g_8 = 0x59B8BC58L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int32_t l_7 = 7L;
    g_8 &= ((safe_unary_minus_func_uint8_t_u((~(safe_add_func_uint16_t_u_u((g_6 <= l_7), g_6))))) >= (-4L));
    return l_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
