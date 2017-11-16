// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_328.c
#include "csmith.h"


static long __undefined;



static uint16_t g_3 = 65535UL;
static uint8_t g_7 = 0x36L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_2 = 0xFD41E559L;
    int32_t l_6 = (-4L);
    int32_t l_8 = (-6L);
    g_3 = l_2;
    l_8 |= ((safe_rshift_func_int16_t_s_s((g_7 |= l_6), 15)) ^ g_3);
    return l_6;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
