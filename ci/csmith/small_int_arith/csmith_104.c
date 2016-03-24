// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_104.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 0x0F57A7C2L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int32_t l_2 = 3L;
    int32_t l_6 = 0x6A3367F5L;
    uint8_t l_7 = 0UL;
    g_3 = l_2;
    l_6 = (l_2 = (safe_rshift_func_int16_t_s_u(g_3, 0)));
    return l_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
