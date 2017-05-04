// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_373.c
#include "csmith.h"


static long __undefined;



static uint32_t g_7 = 0UL;
static int8_t g_12 = 0x86L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint8_t l_2 = 255UL;
    int32_t l_5 = 0xFFB871C7L;
    int32_t l_6 = 1L;
    l_2++;
    --g_7;
    g_12 = (safe_mod_func_int16_t_s_s((l_6 = g_7), l_5));
    return g_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
