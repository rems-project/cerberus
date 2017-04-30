// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o gen/csmith_07.c
#include "csmith.h"


static long __undefined;



static uint32_t g_6 = 0xFA5C62E0L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int8_t l_4 = 0x69L;
    int32_t l_5 = 0L;
    l_5 |= (safe_mul_func_uint8_t_u_u(l_4, 0xC2L));
    return g_6;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
