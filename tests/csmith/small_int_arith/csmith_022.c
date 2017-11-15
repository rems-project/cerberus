// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_022.c
#include "csmith.h"


static long __undefined;



static uint8_t g_7 = 255UL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int16_t l_6 = 1L;
    int32_t l_8 = 0xD3C891C5L;
    uint32_t l_9 = 18446744073709551615UL;
    int32_t l_10 = (-1L);
    int32_t l_13 = 0x1E1C5A3DL;
    uint8_t l_14 = 0xCFL;
    l_10 = (safe_sub_func_int8_t_s_s((((safe_mul_func_int16_t_s_s((l_8 = (g_7 &= l_6)), l_6)) || l_8) && l_8), l_9));
    l_13 = (((l_10 = ((safe_mul_func_int16_t_s_s((((l_8 = (g_7 , g_7)) > g_7) && 4UL), g_7)) , g_7)) < l_9) , 1L);
    ++l_14;
    return g_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
