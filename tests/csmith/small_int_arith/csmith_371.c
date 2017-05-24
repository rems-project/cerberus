// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_371.c
#include "csmith.h"


static long __undefined;



static int64_t g_4 = (-1L);
static uint64_t g_5 = 0x88E1B61BAB593421LL;
static int32_t g_8 = 7L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_6 = 0x78DC2A82L;
    uint64_t l_7 = 1UL;
    g_8 &= ((safe_div_func_uint8_t_u_u(((((((g_5 = (g_4 , g_4)) & g_4) ^ g_4) < l_6) , g_4) == g_4), l_6)) ^ l_7);
    return l_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
