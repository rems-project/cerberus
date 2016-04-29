// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_068.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 0UL;
static uint32_t g_5 = 1UL;
static uint8_t g_10 = 0x9DL;
static int32_t g_15 = (-1L);
static uint32_t g_16 = 3UL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint32_t l_6 = 4294967295UL;
    int32_t l_7 = 5L;
    int32_t l_8 = 0xB61BAB59L;
    if (((safe_div_func_uint32_t_u_u(((g_5 = g_4) >= l_6), l_6)) <= g_4))
    { 
        int8_t l_9 = 1L;
        g_10--;
        l_8 = ((safe_mul_func_int8_t_s_s(0x43L, 0x4CL)) , g_5);
        g_15 = l_9;
    }
    else
    { 
        g_16++;
    }
    return g_16;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
