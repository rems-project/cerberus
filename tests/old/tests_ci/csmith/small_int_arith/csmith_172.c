// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_172.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2 = 18446744073709551615UL;
static int64_t g_3 = 1L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int16_t l_10 = 4L;
    int32_t l_11 = 0x950707DFL;
    g_3 = g_2;
    l_11 = (safe_rshift_func_uint16_t_u_u((safe_add_func_int32_t_s_s(((safe_mod_func_int32_t_s_s(g_2, g_2)) , l_10), 0x921DED68L)), 4));
    return l_11;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
