// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_055.c
#include "csmith.h"


static long __undefined;



static int64_t g_6 = 0xD4351CDCB363F9E9LL;
static uint64_t g_7 = 2UL;
static int16_t g_33 = 0L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int8_t l_2 = 0L;
    int32_t l_3 = (-9L);
    int32_t l_4 = 0L;
    int32_t l_5 = 0x45F1DBECL;
    int32_t l_26 = 0xE468A07CL;
    uint64_t l_37 = 18446744073709551614UL;
    ++g_7;
    for (l_3 = (-26); (l_3 != 1); l_3 = safe_add_func_uint64_t_u_u(l_3, 9))
    { 
        int64_t l_27 = 0xEB4495231FBF6859LL;
        int32_t l_28 = 0L;
        l_28 = (safe_div_func_int32_t_s_s(((((safe_div_func_int32_t_s_s((safe_sub_func_int64_t_s_s((safe_sub_func_uint32_t_u_u((safe_div_func_int8_t_s_s((safe_lshift_func_uint8_t_u_u((safe_lshift_func_int8_t_s_s(0x2BL, g_6)), 2)), l_26)), g_7)), l_27)), g_7)) != 0xD6A56C37L) > l_27) , g_7), g_6));
        l_28 = (g_33 = (safe_lshift_func_int8_t_s_u((safe_div_func_int8_t_s_s((-1L), g_6)), l_28)));
        l_5 = (safe_unary_minus_func_int64_t_s((g_33 || 0UL)));
    }
    l_3 = ((safe_add_func_int64_t_s_s(l_37, g_6)) <= g_33);
    return g_33;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_33, "g_33", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
