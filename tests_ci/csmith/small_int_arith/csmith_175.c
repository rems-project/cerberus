// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_175.c
#include "csmith.h"


static long __undefined;



static uint8_t g_6 = 1UL;
static uint64_t g_7 = 0x4EA6801FC3EEE2FDLL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint8_t l_12 = 1UL;
    int32_t l_13 = (-1L);
    g_7 ^= (safe_mod_func_int64_t_s_s((safe_sub_func_int16_t_s_s((-5L), g_6)), 7L));
    for (g_6 = 25; (g_6 <= 7); g_6 = safe_sub_func_uint8_t_u_u(g_6, 7))
    { 
        l_13 &= (safe_div_func_uint8_t_u_u(((l_12 == g_7) && 255UL), g_7));
    }
    return l_12;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
