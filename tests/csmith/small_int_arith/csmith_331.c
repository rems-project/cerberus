// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_331.c
#include "csmith.h"


static long __undefined;



static uint16_t g_7 = 65535UL;
static int32_t g_8 = 0xB32A831DL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint8_t l_6 = 0xDEL;
    g_8 = ((((g_7 = (safe_unary_minus_func_uint32_t_u((!(((safe_mul_func_int8_t_s_s(l_6, 1L)) < l_6) > 65535UL))))) < g_8) , g_7) == g_8);
    return g_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
