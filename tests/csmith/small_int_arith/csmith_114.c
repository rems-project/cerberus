// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_114.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2 = 5UL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint32_t l_3 = 0x7632667AL;
    int32_t l_6 = 2L;
    int32_t l_7 = 0x673292C5L;
    int32_t l_12 = 1L;
    l_3 = g_2;
    l_7 = (l_6 = (safe_sub_func_int8_t_s_s(((((l_3 && 1L) & l_3) , g_2) , 0x9CL), 0L)));
    l_12 = (safe_mul_func_int8_t_s_s((((((safe_lshift_func_uint16_t_u_s(g_2, 6)) <= l_3) , l_12) ^ l_7) , l_3), g_2));
    return l_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
