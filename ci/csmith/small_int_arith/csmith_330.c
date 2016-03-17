// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_330.c
#include "csmith.h"


static long __undefined;



static uint32_t g_7 = 5UL;
static uint8_t g_8 = 0xF9L;
static uint64_t g_9 = 7UL;
static uint64_t g_13 = 0x720348F4A8FE2430LL;
static uint32_t g_17 = 0xFA48A2B8L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint32_t l_2 = 4294967286UL;
    int32_t l_3 = (-9L);
    uint64_t l_12 = 0x9E9D60A2215256EELL;
    uint32_t l_16 = 9UL;
    l_3 = l_2;
    g_9 = (~((((g_8 = (((safe_mul_func_uint16_t_u_u(g_7, 0x37C0L)) == g_7) | 0x146CDEAD9BACC5D9LL)) < g_7) , l_3) , l_3));
    g_13 = ((safe_sub_func_uint64_t_u_u(l_3, l_3)) & l_12);
    g_17 = (((safe_rshift_func_uint8_t_u_s((g_8 = 0xF8L), l_16)) , g_13) , l_16);
    return l_12;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
