// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_023.c
#include "csmith.h"


static long __undefined;



static uint16_t g_5 = 0xC9FBL;
static uint64_t g_6 = 0x2C25FCC58A012E1DLL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int8_t l_4 = 0x49L;
    g_6 = (((safe_lshift_func_uint8_t_u_u(((0xA7L == 249UL) | l_4), 6)) , g_5) < g_5);
    return g_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
