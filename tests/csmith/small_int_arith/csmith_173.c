// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_173.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static uint64_t g_5 = 0UL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    for (g_2 = 0; (g_2 == 24); g_2 = safe_add_func_uint8_t_u_u(g_2, 1))
    { 
        g_5 = g_2;
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
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
