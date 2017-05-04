// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_053.c
#include "csmith.h"


static long __undefined;



static uint32_t g_8 = 0xAFCB143EL;
static uint8_t g_9 = 7UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int8_t l_4 = (-4L);
    int32_t l_5 = 7L;
    l_5 &= (safe_mod_func_uint32_t_u_u(l_4, 0xD95E17CAL));
    g_9 = (safe_add_func_uint64_t_u_u(((l_4 != 4294967291UL) , l_5), g_8));
    return g_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
