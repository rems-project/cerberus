// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_334.c
#include "csmith.h"


static long __undefined;



static int32_t g_4 = 3L;
static int8_t g_5 = (-1L);
static uint16_t g_9 = 0x59CDL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int8_t l_6 = 1L;
    int32_t l_10 = 0L;
    g_4 = (safe_rshift_func_int8_t_s_u(((g_5 ^= g_4) && l_6), g_4));
    g_4 = ((l_10 ^= (((safe_div_func_uint64_t_u_u((g_4 & g_9), g_4)) | l_6) < g_9)) , l_10);
    return g_9;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
