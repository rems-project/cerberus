// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_400.c
#include "csmith.h"


static long __undefined;



static int8_t g_3 = (-7L);
static uint64_t g_4 = 18446744073709551608UL;
static int32_t g_26 = 0x99EA7EB8L;
static int64_t g_28 = 0x20B275CF8B874BDBLL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint32_t l_2 = 0x3198A8F9L;
    int32_t l_27 = 0x2BBD4AA4L;
    uint32_t l_32 = 0x8319B885L;
    if (l_2)
    { 
        uint32_t l_25 = 0x510AFBD1L;
        g_4 = (g_3 || (-4L));
        for (l_2 = 0; (l_2 != 49); l_2 = safe_add_func_uint16_t_u_u(l_2, 5))
        { 
            uint32_t l_11 = 0xEF054A20L;
            int32_t l_12 = 0x2CB3A3FCL;
            l_12 = (safe_mod_func_int16_t_s_s((safe_sub_func_int16_t_s_s(g_3, 0L)), l_11));
        }
        g_28 = (safe_add_func_int16_t_s_s(((+(safe_mul_func_uint16_t_u_u((safe_add_func_int16_t_s_s((safe_div_func_uint8_t_u_u((l_27 = ((((safe_mod_func_uint32_t_u_u((+(g_26 ^= ((l_25 , l_2) && 1L))), 0x36DC9922L)) != 1L) <= l_2) , 253UL)), l_25)), g_4)), l_2))) || g_26), l_2));
        l_27 &= (-1L);
    }
    else
    { 
        uint8_t l_29 = 7UL;
        int32_t l_33 = 3L;
        l_29--;
        l_33 = (g_3 <= l_32);
    }
    return l_27;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
