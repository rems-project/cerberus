// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_222.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 1L;
static uint8_t g_28 = 0UL;
static int32_t g_31 = 0L;
static int8_t g_32 = 0xABL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_9 = 0xA3A11C157478144ALL;
    int32_t l_10 = 0L;
    for (g_2 = 0; (g_2 >= (-15)); g_2--)
    { 
        int64_t l_11 = 1L;
        uint32_t l_27 = 1UL;
        l_11 = ((safe_rshift_func_uint16_t_u_u((l_9 ^= (safe_div_func_uint32_t_u_u(g_2, g_2))), l_10)) , 0xD67A4BEDL);
        l_10 = (((safe_add_func_int64_t_s_s((safe_sub_func_int16_t_s_s(((safe_mul_func_uint8_t_u_u((safe_sub_func_int8_t_s_s(((safe_rshift_func_uint8_t_u_s(((!(safe_mul_func_int8_t_s_s((l_27 |= (safe_mul_func_uint16_t_u_u(l_11, 0x12A7L))), g_2))) >= g_2), l_10)) & l_10), 0x7AL)), g_2)) ^ g_2), g_2)), l_11)) >= g_2) || 0x5EC41505L);
        g_28 = (((g_2 , g_2) == g_2) && g_2);
        g_32 &= (((g_31 = ((safe_rshift_func_uint16_t_u_s(l_10, l_11)) , 1L)) || l_10) >= l_27);
    }
    return l_10;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    transparent_crc(g_32, "g_32", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
