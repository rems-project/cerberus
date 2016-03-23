// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_199.c
#include "csmith.h"


static long __undefined;



static uint32_t g_5 = 18446744073709551615UL;
static uint32_t g_12 = 0xD7839892L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint8_t l_2 = 8UL;
    int16_t l_10 = 0x25FCL;
    int32_t l_11 = 0x12E1DFE0L;
    int32_t l_13 = (-1L);
    l_13 = (g_12 = (((g_5 = (l_2++)) && (l_11 = (l_10 = ((safe_sub_func_uint16_t_u_u((safe_mod_func_int32_t_s_s((-8L), g_5)), g_5)) , l_2)))) || g_5));
    return l_11;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
