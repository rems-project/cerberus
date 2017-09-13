// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_198.c
#include "csmith.h"


static long __undefined;



static int16_t g_9 = 0xC553L;
static int32_t g_10 = 0x6F7FBF21L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint8_t l_8 = 255UL;
    g_10 |= (safe_add_func_int16_t_s_s((safe_div_func_int64_t_s_s(((safe_lshift_func_uint8_t_u_s(l_8, 7)) > 0xA9L), g_9)), l_8));
    return g_10;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
