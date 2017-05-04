// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_205.c
#include "csmith.h"


static long __undefined;



static uint32_t g_8 = 0xEEDA5852L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int8_t l_6 = 1L;
    int32_t l_7 = 0x76D6092FL;
    int32_t l_9 = 1L;
    int32_t l_10 = 0x56E700D6L;
    l_10 &= (l_9 |= (((((safe_lshift_func_uint8_t_u_s((safe_lshift_func_int8_t_s_u((l_7 = (((l_6 && l_6) >= 1L) <= l_6)), 4)), 2)) < g_8) & l_6) < 0x0A5DL) >= g_8));
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
