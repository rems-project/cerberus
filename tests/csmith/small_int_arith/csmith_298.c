// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_298.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 4294967295UL;
static int8_t g_3 = 0xFEL;
static int64_t g_8 = 2L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint32_t l_4 = 4294967287UL;
    int32_t l_5 = 0x25260417L;
    g_3 = g_2;
    l_5 = l_4;
    g_8 = (safe_mod_func_int64_t_s_s((((((g_3 |= l_5) < g_2) || l_4) , g_2) , 6L), l_4));
    return l_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
