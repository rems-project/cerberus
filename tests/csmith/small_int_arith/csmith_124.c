// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_124.c
#include "csmith.h"


static long __undefined;



static int8_t g_4 = 8L;
static uint64_t g_6 = 0x1220985A9576C3A0LL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint8_t l_5 = 2UL;
    int32_t l_9 = 0x15898F01L;
    g_6 = (safe_add_func_int32_t_s_s((g_4 > 0x00L), l_5));
    l_9 = (safe_mod_func_int64_t_s_s(0x143E95AAD8530DE9LL, l_5));
    return l_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
