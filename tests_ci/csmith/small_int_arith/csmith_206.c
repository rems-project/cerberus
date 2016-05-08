// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_206.c
#include "csmith.h"


static long __undefined;



static uint64_t g_12 = 0x1637C1D6B3BFA32ALL;
static int64_t g_15 = (-3L);
static uint16_t g_18 = 0x6C4AL;
static uint8_t g_25 = 1UL;
static int32_t g_35 = 0x8BEE6DABL;
static int64_t g_41 = 0x364F2CA12535B5B0LL;
static uint8_t g_53 = 0xF1L;
static int64_t g_65 = 9L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_4 = 0x0B4FFB87L;
    int8_t l_5 = 0L;
    int32_t l_33 = 0x025EC560L;
    uint16_t l_52 = 0xDFD6L;
    int32_t l_54 = 0xE38EDFC7L;
    if ((safe_sub_func_uint32_t_u_u((l_4 , l_5), l_5)))
    { 
        uint32_t l_8 = 0x5C9E53E5L;
        for (l_5 = 0; (l_5 < 19); ++l_5)
        { 
            uint8_t l_10 = 0xF3L;
            int32_t l_16 = 0x586FD5D7L;
            int32_t l_17 = (-1L);
            l_8 = (6UL > 0L);
            if (l_8)
            { 
                uint8_t l_9 = 0UL;
                l_10 &= ((l_5 , l_9) | l_4);
            }
            else
            { 
                int8_t l_11 = 0xC0L;
                g_12++;
                return g_12;
            }
            g_18--;
        }
        return g_15;
    }
    else
    { 
        uint32_t l_32 = 0UL;
        int8_t l_34 = 1L;
        g_25 = (safe_sub_func_uint16_t_u_u((safe_add_func_uint8_t_u_u(g_12, g_15)), 0xFAABL));
        g_35 = (safe_div_func_uint64_t_u_u(((((l_33 ^= ((safe_div_func_int16_t_s_s((safe_mod_func_uint32_t_u_u(l_32, g_12)), 0xFE92L)) >= l_32)) | g_15) , l_34) | l_34), g_12));
        if ((l_33 = (safe_mul_func_uint8_t_u_u((((g_41 &= ((safe_unary_minus_func_uint16_t_u(((((g_35 = ((safe_lshift_func_int16_t_s_u((l_34 && g_25), l_5)) <= 0xD9L)) && 0xDB1D70F3L) || g_35) ^ 255UL))) && l_34)) , 255UL) <= 0xD8L), g_15))))
        { 
            g_35 ^= (safe_unary_minus_func_int8_t_s((l_32 | l_34)));
        }
        else
        { 
            uint32_t l_45 = 4294967288UL;
            g_35 ^= ((safe_div_func_int8_t_s_s((0xAE0CD5C0F4FD1A68LL ^ l_45), g_15)) | l_45);
        }
        g_35 ^= (safe_lshift_func_int16_t_s_u(l_4, 15));
    }
    l_54 |= (!(g_53 &= (((l_33 = (~(safe_mul_func_uint16_t_u_u(l_52, g_35)))) | g_35) > g_15)));
    g_35 = (l_54 ^= g_12);
    g_35 = (safe_lshift_func_uint16_t_u_u((safe_sub_func_int8_t_s_s((safe_mod_func_uint16_t_u_u((safe_lshift_func_uint16_t_u_s(((safe_mod_func_uint16_t_u_u(((g_65 = (g_35 <= g_15)) && 0x9E61L), g_12)) >= 0x9E20L), l_52)), g_18)), g_25)), g_35));
    return l_54;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    transparent_crc(g_41, "g_41", print_hash_value);
    transparent_crc(g_53, "g_53", print_hash_value);
    transparent_crc(g_65, "g_65", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
