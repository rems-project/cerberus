// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_333.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 2UL;
static int32_t g_7 = 0L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int64_t l_3 = 0x2A43D9532BB11ACCLL;
    int64_t l_6 = 0x374C7AF5AF8B5131LL;
    l_3 = (g_2 & g_2);
    g_7 &= (((safe_lshift_func_uint8_t_u_s(l_3, l_3)) < l_6) != l_3);
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
