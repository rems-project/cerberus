// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_277.c
#include "csmith.h"


static long __undefined;



static int64_t g_6 = 1L;
static uint16_t g_7 = 0x8BEAL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int32_t l_8 = 0x66BAFCB1L;
    int32_t l_9 = 0xD8530DE9L;
    int32_t l_10 = (-1L);
    l_9 ^= (safe_rshift_func_int8_t_s_s((safe_lshift_func_int8_t_s_s((g_7 ^= ((g_6 , g_6) | g_6)), g_6)), l_8));
    l_8 = ((((l_10 ^ 0xDFBA22E9L) , g_6) & l_8) | 6L);
    return g_7;
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
