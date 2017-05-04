// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_030.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x1F7E2799L;
static int8_t g_14 = (-1L);



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint32_t l_12 = 4294967287UL;
    int32_t l_20 = (-10L);
    for (g_2 = 10; (g_2 > (-11)); g_2 = safe_sub_func_int32_t_s_s(g_2, 4))
    { 
        int8_t l_15 = 0x78L;
        int32_t l_22 = 0x67BB1A88L;
        if (((((safe_rshift_func_uint16_t_u_s((g_2 != g_2), g_2)) && g_2) , 0x2FL) > g_2))
        { 
            int8_t l_13 = 0x10L;
            l_15 = (safe_mod_func_uint64_t_u_u((+(safe_add_func_uint64_t_u_u(((g_14 ^= (((l_12 & 6L) , l_13) != 0xA75A592C6EED1E12LL)) >= 1L), 0xE0FC36FE5AB06C0ELL))), 0x32C5B641B44ADCA1LL));
        }
        else
        { 
            int32_t l_34 = (-2L);
            for (l_12 = 3; (l_12 == 9); ++l_12)
            { 
                uint32_t l_21 = 0xFE0CD1B7L;
                int32_t l_27 = 1L;
                l_22 = ((((safe_rshift_func_uint16_t_u_u(g_14, 13)) <= l_20) , l_21) <= g_2);
                l_27 |= (safe_rshift_func_uint16_t_u_s((safe_add_func_int8_t_s_s(g_14, g_2)), 7));
            }
            for (g_14 = 0; (g_14 <= 12); g_14++)
            { 
                int32_t l_35 = 0x1CF717C9L;
                l_35 &= (safe_rshift_func_int16_t_s_s((((safe_sub_func_uint8_t_u_u(255UL, g_14)) != 0UL) < g_2), l_34));
            }
            if (g_2)
                break;
        }
    }
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
