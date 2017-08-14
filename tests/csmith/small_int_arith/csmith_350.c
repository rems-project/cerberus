// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_350.c
#include "csmith.h"


static long __undefined;



static uint8_t g_8 = 4UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int8_t l_9 = 0x5EL;
    int32_t l_10 = 1L;
    uint16_t l_11 = 65532UL;
    l_10 = (safe_lshift_func_uint16_t_u_u((safe_mod_func_uint64_t_u_u((l_9 = (((safe_sub_func_int32_t_s_s(0L, 3L)) && 0xA1BF2B29949DFCF0LL) >= g_8)), g_8)), 4));
    return l_11;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
