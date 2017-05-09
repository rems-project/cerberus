// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_293.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0xF825E7A66FE7D8A8LL;
static int16_t g_4 = 0x3B9DL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_3 = 1UL;
    l_3 = g_2;
    g_4 = 8L;
    return l_3;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
