// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_084.c
#include "csmith.h"


static long __undefined;



static uint32_t g_8 = 4294967286UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int32_t l_7 = 0x94FE5F36L;
    g_8 = (safe_div_func_uint64_t_u_u(((+(safe_mul_func_uint8_t_u_u((0x506EL & l_7), 0x8DL))) || 65535UL), 0xE9323D1BCA9D6923LL));
    return g_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
