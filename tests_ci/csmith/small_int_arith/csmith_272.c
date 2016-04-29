// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_272.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 0x6B0FL;
static int32_t g_5 = 0x5CABFC39L;
static int64_t g_9 = 2L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint64_t l_3 = 0x99CFE04822B16580LL;
    int32_t l_4 = 5L;
    uint32_t l_6 = 0x3E0566A9L;
    g_2 = (-5L);
    g_5 = ((g_2 = (l_3 != g_2)) , l_4);
    l_6 = (g_5 && g_2);
    for (l_4 = 0; (l_4 >= (-5)); --l_4)
    { 
        uint8_t l_12 = 8UL;
        int32_t l_13 = 3L;
        g_9 = (g_5 = (l_4 || g_5));
        g_5 = (((safe_rshift_func_int16_t_s_u((l_13 ^= l_12), 1)) < g_9) < 0x8BD8L);
    }
    return g_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
