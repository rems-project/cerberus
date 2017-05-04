// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_123.c
#include "csmith.h"


static long __undefined;



static int32_t g_4 = 0x9D29BE1DL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint16_t l_5 = 65532UL;
    uint8_t l_8 = 0x9EL;
    l_5 = (safe_mod_func_int8_t_s_s(1L, g_4));
    for (l_5 = 26; (l_5 <= 6); l_5 = safe_sub_func_int32_t_s_s(l_5, 7))
    { 
        l_8--;
    }
    return l_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
