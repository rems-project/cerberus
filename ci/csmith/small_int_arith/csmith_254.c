// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_254.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x2C03342EL;
static uint32_t g_7 = 0x22263126L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int32_t l_8 = 0x1D8F8F57L;
    for (g_2 = (-5); (g_2 != 6); g_2++)
    { 
        if (g_2)
            break;
        g_7 = (safe_mod_func_uint32_t_u_u(0UL, 0xB6182EACL));
    }
    g_2 = (l_8 && l_8);
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
