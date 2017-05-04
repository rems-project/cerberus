// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_245.c
#include "csmith.h"


static long __undefined;



static int32_t g_6 = 0x885C6F1BL;
static int32_t g_7 = 0x60B0CEAFL;
static int16_t g_8 = 0x6DD8L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int64_t l_9 = 1L;
    l_9 |= (safe_lshift_func_uint16_t_u_s((g_8 = (safe_sub_func_uint16_t_u_u((g_7 = g_6), g_6))), 1));
    return l_9;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
