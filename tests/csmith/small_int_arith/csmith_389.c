// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_389.c
#include "csmith.h"


static long __undefined;



static uint64_t g_8 = 0x672A8358BD4DFBD6LL;
static int16_t g_10 = 0x7CD9L;
static int32_t g_11 = 0xD94E8FE7L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint8_t l_9 = 0xECL;
    int32_t l_16 = 0x3F3AC9D7L;
    int32_t l_17 = 0x9A07B304L;
    g_10 = ((safe_mod_func_uint64_t_u_u(((safe_div_func_uint32_t_u_u(((safe_mul_func_uint16_t_u_u(65526UL, 65526UL)) >= g_8), 0x021C3A23L)) == l_9), 0x43AC46DDCD16652DLL)) >= g_8);
    g_11 |= ((g_8 , g_8) > g_10);
    l_17 = (safe_sub_func_int16_t_s_s((l_16 |= (safe_rshift_func_int8_t_s_s(l_9, 0))), l_9));
    return l_9;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
