// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_370.c
#include "csmith.h"


static long __undefined;



static uint32_t g_5 = 0xAD386CCEL;
static int16_t g_10 = 2L;
static int8_t g_13 = (-1L);
static uint32_t g_14 = 0xF2D3F504L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int8_t l_4 = (-5L);
    int32_t l_11 = (-5L);
    int32_t l_12 = 1L;
    l_11 = ((safe_rshift_func_uint16_t_u_s((++g_5), (safe_div_func_uint64_t_u_u(l_4, g_10)))) , l_4);
    g_14++;
    return l_11;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
