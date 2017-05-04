// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_038.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0x5E7A66FE7D8A8701LL;
static uint32_t g_6 = 0xB60E704FL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int8_t l_3 = 0L;
    l_3 = g_2;
    g_6 = (safe_div_func_int64_t_s_s((((0x2AL != g_2) > g_2) ^ l_3), l_3));
    return g_6;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
