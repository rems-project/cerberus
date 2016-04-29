// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_367.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x1F7E2799L;
static int32_t g_9 = 9L;
static int16_t g_11 = 0xA75AL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int64_t l_8 = 0x5F0B101AAE4B9A73LL;
    for (g_2 = 6; (g_2 > 5); g_2--)
    { 
        uint32_t l_7 = 9UL;
        int16_t l_10 = 0L;
        g_11 = (((g_9 |= ((l_8 = ((safe_div_func_int32_t_s_s(((l_7 &= (g_2 && 0UL)) , (-6L)), 0xA4AD744DL)) , 0x69576881L)) , l_8)) == l_10) , l_10);
    }
    return l_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
