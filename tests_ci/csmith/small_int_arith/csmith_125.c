// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_125.c
#include "csmith.h"


static long __undefined;



static int8_t g_9 = 0L;
static int16_t g_26 = 3L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_3 = 0x5596960FL;
    int32_t l_4 = 0x070ADE21L;
    l_4 |= (!(l_3 , l_3));
    if (((safe_sub_func_uint64_t_u_u(((safe_sub_func_int64_t_s_s((g_9 == l_4), 0UL)) , g_9), g_9)) ^ 0x5AE649F6L))
    { 
        uint32_t l_25 = 0UL;
        l_4 = (safe_rshift_func_uint16_t_u_u((safe_mul_func_uint8_t_u_u((safe_sub_func_uint16_t_u_u((safe_mod_func_int64_t_s_s((safe_rshift_func_int8_t_s_s((+(safe_mul_func_uint16_t_u_u(((safe_mod_func_uint32_t_u_u(0xBFB66FEBL, l_3)) | g_9), g_9))), 7)), 4UL)), l_25)), l_25)), 6));
        l_4 &= (g_26 ^= (l_25 , 0x86335C0DL));
    }
    else
    { 
        int16_t l_29 = 0L;
        l_4 ^= ((safe_rshift_func_uint8_t_u_s(((-7L) || l_3), g_9)) != l_29);
    }
    return g_26;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
