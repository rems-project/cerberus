// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_091.c
#include "csmith.h"


static long __undefined;



static uint64_t g_9 = 0UL;
static int32_t g_11 = 0x88146CDEL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_10 = 0x3ED15DE05DAE5A60LL;
    g_11 |= (safe_div_func_int32_t_s_s((safe_rshift_func_int8_t_s_s((+(safe_rshift_func_int16_t_s_s((g_9 > l_10), l_10))), l_10)), 4294967288UL));
    return l_10;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
