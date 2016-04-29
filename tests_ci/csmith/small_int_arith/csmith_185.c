// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_185.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = (-10L);
static uint64_t g_5 = 0xA756A3367F5ED9A9LL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint8_t l_3 = 0UL;
    int32_t l_4 = 0xE2167FA5L;
    l_4 = (l_3 ^= (g_2 < g_2));
    g_5--;
    return l_3;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
