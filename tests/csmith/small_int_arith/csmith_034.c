// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_034.c
#include "csmith.h"


static long __undefined;



static int16_t g_4 = 8L;
static uint64_t g_7 = 2UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int32_t l_5 = 1L;
    int32_t l_6 = 0L;
    g_7 &= (((safe_mod_func_uint16_t_u_u((l_5 = ((g_4 > l_5) , l_5)), l_6)) ^ g_4) , g_4);
    l_6 = (safe_lshift_func_int8_t_s_u(l_5, 6));
    return l_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
