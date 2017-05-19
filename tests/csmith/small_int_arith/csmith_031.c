// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_031.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xA0256915L;
static int16_t g_16 = (-1L);
static int32_t g_20 = 0x5FAFE44FL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int8_t l_6 = (-1L);
    int32_t l_7 = 1L;
    g_2 = g_2;
    for (g_2 = (-21); (g_2 != (-5)); g_2 = safe_add_func_int16_t_s_s(g_2, 9))
    { 
        int16_t l_14 = (-1L);
        uint8_t l_15 = 0xCFL;
        uint16_t l_19 = 0UL;
        l_6 &= (safe_unary_minus_func_int64_t_s(0x6E5C7A00F47A6DEELL));
        l_7 = (65533UL <= 0x1669L);
        g_16 = (((safe_lshift_func_uint8_t_u_s((((((((safe_add_func_int16_t_s_s(((safe_lshift_func_uint16_t_u_u(((l_14 , 0xEC299E88L) >= l_15), 1)) & 0x0F2D6273D5943E2FLL), g_2)) & 0xDDB8L) == 0x869BL) | l_15) && 0UL) | 0xFF44L) != 0x28L), 1)) ^ l_6) ^ g_2);
        for (l_15 = 3; (l_15 >= 6); ++l_15)
        { 
            l_19 ^= g_2;
            g_20 = g_2;
        }
    }
    return g_20;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
