// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_316.c
#include "csmith.h"


static long __undefined;



static uint16_t g_4 = 65535UL;
static uint8_t g_7 = 0UL;
static uint64_t g_12 = 0UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int32_t l_5 = 0x8BAC04EEL;
    int32_t l_6 = (-1L);
    uint64_t l_11 = 18446744073709551608UL;
    l_6 = ((safe_mul_func_uint8_t_u_u((g_4 | l_5), g_4)) > g_4);
    g_7 = l_5;
    l_6 = (g_12 = (!((safe_sub_func_int8_t_s_s(l_6, l_11)) , g_7)));
    l_6 = (safe_mod_func_uint64_t_u_u(((safe_rshift_func_uint16_t_u_s((safe_mul_func_uint8_t_u_u(((safe_mul_func_uint16_t_u_u((safe_rshift_func_int16_t_s_s((safe_rshift_func_int8_t_s_s(g_7, 7)), l_11)), 0xDB82L)) != (-1L)), (-3L))), g_7)) == l_11), g_7));
    return l_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
