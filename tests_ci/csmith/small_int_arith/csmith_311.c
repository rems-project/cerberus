// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_311.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x97F6AF11L;
static int8_t g_7 = 0x5AL;
static uint8_t g_9 = 250UL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int64_t l_10 = 1L;
    for (g_2 = (-14); (g_2 > (-7)); g_2 = safe_add_func_int32_t_s_s(g_2, 8))
    { 
        uint32_t l_8 = 0x21591249L;
        g_9 ^= (safe_div_func_uint64_t_u_u(g_7, l_8));
    }
    return l_10;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
