// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_145.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-8L);
static int8_t g_5 = 0L;
static int32_t g_8 = 0xD080C170L;
static uint16_t g_9 = 65535UL;
static uint64_t g_23 = 0xDF0EBF90350D8AF8LL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint16_t l_14 = 0x9876L;
    int8_t l_15 = (-1L);
    int32_t l_26 = 0L;
    for (g_2 = 0; (g_2 == 15); g_2 = safe_add_func_int64_t_s_s(g_2, 6))
    { 
        uint16_t l_22 = 1UL;
        g_5 ^= 0L;
        for (g_5 = 27; (g_5 > 12); g_5 = safe_sub_func_uint64_t_u_u(g_5, 4))
        { 
            ++g_9;
            return g_8;
        }
        g_8 = (((l_14 = (safe_rshift_func_int8_t_s_s(g_2, 5))) , l_15) == g_5);
        g_23 = (g_8 = (safe_add_func_int16_t_s_s((safe_sub_func_uint64_t_u_u((safe_div_func_uint32_t_u_u(l_14, g_5)), 4L)), l_22)));
    }
    l_26 = (safe_mod_func_int16_t_s_s(l_15, g_23));
    g_2 = ((safe_mul_func_int16_t_s_s(((safe_rshift_func_int8_t_s_s((safe_lshift_func_uint8_t_u_s((safe_div_func_uint32_t_u_u(((g_9 , (-3L)) >= g_2), (-6L))), 7)), 2)) , (-4L)), l_26)) , 0xE05243B9L);
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
