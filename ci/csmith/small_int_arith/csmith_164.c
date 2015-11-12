// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_164.c
#include "csmith.h"


static long __undefined;



static int32_t g_6 = (-1L);
static uint16_t g_11 = 65533UL;
static uint64_t g_14 = 18446744073709551615UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_7 = 3UL;
    int32_t l_8 = (-1L);
    l_8 = (((((safe_div_func_int64_t_s_s((safe_mod_func_int8_t_s_s(g_6, l_7)), l_7)) <= g_6) <= 1UL) | g_6) | l_7);
    l_8 = ((safe_lshift_func_int8_t_s_s((g_6 ^ g_11), g_6)) > 0xECF7921E124DC41FLL);
    for (g_6 = (-2); (g_6 != (-21)); g_6--)
    { 
        return g_6;
    }
    g_14 = ((l_8 = 0xAD816F93L) , g_11);
    return l_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
