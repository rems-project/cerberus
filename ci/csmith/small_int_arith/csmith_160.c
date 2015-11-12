// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_160.c
#include "csmith.h"


static long __undefined;



static uint16_t g_7 = 0UL;
static uint64_t g_8 = 0xFD947597A61EEFB6LL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int32_t l_4 = 0xFCB50BF3L;
    int32_t l_5 = 0xE77DD688L;
    int32_t l_6 = 0xA1E94870L;
    l_6 = (l_5 = (safe_mul_func_int16_t_s_s(l_4, 65532UL)));
    g_8 = (g_7 == l_5);
    l_5 = l_6;
    l_5 = (safe_lshift_func_int16_t_s_u((g_8 & 0x85A7L), g_8));
    return g_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
