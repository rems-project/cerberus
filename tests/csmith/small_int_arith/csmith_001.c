// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o gen/csmith_01.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 1L;
static int32_t g_19 = 0x65C829EDL;



static int32_t  func_1(void);



static int32_t  func_1(void)
{ 
    int64_t l_2 = 0L;
    g_3 = l_2;
    for (g_3 = 0; (g_3 < 25); g_3 = safe_add_func_uint16_t_u_u(g_3, 7))
    { 
        int8_t l_18 = (-3L);
        int32_t l_20 = 0xCADD6352L;
        l_20 = ((((((safe_sub_func_int64_t_s_s((safe_div_func_uint16_t_u_u((safe_add_func_int8_t_s_s((safe_rshift_func_int8_t_s_u(((((safe_rshift_func_uint8_t_u_u(((safe_rshift_func_int16_t_s_u(l_18, g_3)) > l_18), 4)) < 1UL) >= l_2) < l_2), 5)), g_19)), g_19)), g_3)) && g_19) >= g_19) , (-9L)) >= 18446744073709551606UL) , (-3L));
        return l_18;
    }
    g_3 = l_2;
    return g_19;
}




int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
