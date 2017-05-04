// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_051.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0x648261F9L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int16_t l_9 = (-3L);
    uint32_t l_10 = 1UL;
    int32_t l_11 = (-10L);
    g_2--;
    l_11 = (safe_mod_func_int32_t_s_s(((safe_add_func_int64_t_s_s(((l_9 ^ 0xED9BA07EL) , l_9), g_2)) & l_10), 0xDF3D37A5L));
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
