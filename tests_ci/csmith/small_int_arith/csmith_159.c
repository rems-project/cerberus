// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_159.c
#include "csmith.h"


static long __undefined;



static int16_t g_8 = 0xB2B5L;
static int32_t g_10 = 0x4B0AD8EAL;
static uint16_t g_25 = 0x33D2L;
static uint16_t g_54 = 6UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int16_t l_2 = (-10L);
    int32_t l_3 = 0x417BE187L;
    uint32_t l_7 = 0xA0BDBDF7L;
    int32_t l_59 = 0x7C8CEAAFL;
    if ((l_3 = (l_2 = (0x13532FE2L == 0x32A27689L))))
    { 
        int8_t l_9 = 0xE7L;
        l_3 = 0xA73D2D67L;
        g_10 = ((((safe_add_func_int8_t_s_s((+(l_7 & l_3)), g_8)) > l_2) & l_2) || l_9);
    }
    else
    { 
        uint32_t l_21 = 0xFF79FACDL;
        int32_t l_44 = (-1L);
        for (g_8 = 0; (g_8 >= (-3)); g_8--)
        { 
            uint64_t l_24 = 18446744073709551615UL;
            int32_t l_36 = 0x82467468L;
            for (l_7 = 0; (l_7 != 32); ++l_7)
            { 
                int16_t l_20 = 0x45D7L;
                for (l_3 = 0; (l_3 > 27); ++l_3)
                { 
                    l_21 ^= (safe_lshift_func_int8_t_s_u(((+(-1L)) || l_20), l_20));
                    if (g_10)
                        break;
                }
                l_24 = ((safe_add_func_int32_t_s_s((((l_21 < l_21) , 18446744073709551613UL) , g_10), g_10)) && l_7);
                g_25--;
            }
            if ((safe_add_func_uint16_t_u_u((safe_sub_func_int16_t_s_s((l_21 <= 0L), g_10)), g_10)))
            { 
                g_10 = ((((safe_mul_func_int16_t_s_s(l_2, g_10)) ^ 0xC745D07A051AAF19LL) , 0x5C588CB5L) , g_25);
                if (l_24)
                    continue;
            }
            else
            { 
                uint32_t l_37 = 0xD46C64E7L;
                l_37--;
                for (l_2 = 0; (l_2 <= 18); l_2++)
                { 
                    return g_8;
                }
                for (l_7 = (-23); (l_7 > 5); ++l_7)
                { 
                    l_44 |= (g_10 > l_2);
                    if (l_24)
                        continue;
                    g_10 = (((safe_unary_minus_func_int64_t_s(((((l_44 = (safe_rshift_func_int16_t_s_s((((safe_lshift_func_int8_t_s_u(l_21, 2)) , 0x9A67E99EL) , l_37), 7))) == g_10) , 0x26471B2AL) == g_10))) , 0x870EL) , l_21);
                }
                g_10 = 0L;
            }
        }
        g_54 |= (safe_sub_func_uint8_t_u_u((((safe_lshift_func_int16_t_s_s(((((-1L) && g_25) , g_10) & l_7), l_21)) || 0L) , g_10), 0x50L));
    }
    l_3 = (safe_mod_func_uint8_t_u_u(g_54, l_7));
    l_59 |= ((safe_sub_func_uint8_t_u_u(((l_2 , g_10) ^ l_2), g_10)) ^ l_3);
    return g_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    transparent_crc(g_54, "g_54", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
