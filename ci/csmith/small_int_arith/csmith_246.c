// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_246.c
#include "csmith.h"


static long __undefined;



static int16_t g_4 = 1L;
static uint32_t g_5 = 0x4964A53AL;
static int64_t g_11 = 0xCABFC3938DD44AD3LL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint32_t l_10 = 4294967292UL;
    g_11 = (safe_sub_func_uint8_t_u_u((g_5--), (safe_mul_func_uint8_t_u_u((l_10 = ((g_4 >= g_4) < g_4)), 4UL))));
    return l_10;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
