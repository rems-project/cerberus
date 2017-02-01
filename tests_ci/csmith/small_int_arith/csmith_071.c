// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_071.c
#include "csmith.h"


static long __undefined;



static uint64_t g_9 = 4UL;
static uint64_t g_10 = 18446744073709551615UL;
static int32_t g_15 = (-1L);



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int32_t l_11 = 0x42760385L;
    int32_t l_12 = (-1L);
    int32_t l_16 = 5L;
    l_11 ^= (g_10 &= (safe_div_func_int8_t_s_s((safe_sub_func_uint64_t_u_u((safe_rshift_func_int16_t_s_s(((safe_unary_minus_func_int8_t_s(g_9)) <= 0x39ED080C170CD509LL), g_9)), 0x365653D42374B1B0LL)), 0xCCL)));
    l_12 = 0xEE21AFA9L;
    g_15 = (safe_mod_func_uint32_t_u_u(((7L != (-1L)) <= g_9), g_10));
    l_16 = 0xE713E19FL;
    return g_10;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
