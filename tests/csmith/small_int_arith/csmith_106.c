// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_106.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x90AC204EL;
static uint16_t g_15 = 0xD2CCL;
static uint16_t g_18 = 0UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint32_t l_5 = 0x0197F0A2L;
    int32_t l_14 = 9L;
    for (g_2 = (-13); (g_2 <= 21); g_2 = safe_add_func_int16_t_s_s(g_2, 6))
    { 
        uint8_t l_6 = 1UL;
        l_6 = (l_5 == l_5);
        g_15 = (safe_mul_func_int8_t_s_s(((safe_mod_func_int64_t_s_s((l_14 |= (((((((((safe_lshift_func_uint16_t_u_u((safe_unary_minus_func_uint64_t_u(8UL)), 7)) != 0x20L) | g_2) , 0L) != l_6) >= l_6) > (-1L)) , 0xB9L) < g_2)), g_2)) <= g_2), 0xC4L));
        return l_6;
    }
    g_18 ^= (safe_mul_func_uint16_t_u_u(g_2, l_14));
    return g_18;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
