// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_019.c
#include "csmith.h"


static long __undefined;



static uint8_t g_3 = 1UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint32_t l_2 = 0x6960F57AL;
    int32_t l_8 = (-7L);
    uint64_t l_9 = 18446744073709551608UL;
    g_3 = l_2;
    l_8 |= ((safe_rshift_func_uint8_t_u_s((safe_add_func_int32_t_s_s((g_3 , 0x67F5ED9AL), g_3)), g_3)) & l_2);
    return l_9;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
