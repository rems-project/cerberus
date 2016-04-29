// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_302.c
#include "csmith.h"


static long __undefined;



static uint16_t g_9 = 0xA986L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int8_t l_10 = 6L;
    int16_t l_11 = 0x27F7L;
    int32_t l_12 = 0xD39C7C6FL;
    l_12 = (((safe_add_func_int8_t_s_s((((safe_div_func_int16_t_s_s(((safe_add_func_int8_t_s_s((+g_9), l_10)) > g_9), g_9)) <= l_10) & g_9), 0UL)) <= 0xA8L) & l_11);
    return g_9;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
