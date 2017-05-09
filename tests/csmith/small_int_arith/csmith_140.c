// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_140.c
#include "csmith.h"


static long __undefined;



static int8_t g_6 = 0x2CL;
static int16_t g_7 = (-3L);



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int64_t l_8 = (-1L);
    g_7 = ((safe_lshift_func_uint8_t_u_u((safe_mod_func_uint32_t_u_u(g_6, 7L)), g_6)) < g_6);
    return l_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
