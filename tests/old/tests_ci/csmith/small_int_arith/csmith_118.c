// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_118.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0xFF606579L;
static uint64_t g_6 = 0x4543BEB7161AB6ECLL;
static uint8_t g_10 = 0UL;
static uint32_t g_29 = 1UL;
static int16_t g_30 = 0xD89EL;
static uint64_t g_32 = 0x4E52275DD3610CB4LL;
static int32_t g_35 = 0L;
static uint64_t g_58 = 0xC87C631DBC551464LL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint8_t l_3 = 254UL;
    int32_t l_9 = (-1L);
lbl_18:
    l_3 = g_2;
    if ((((safe_rshift_func_uint8_t_u_u((g_6++), 7)) ^ ((g_10--) | l_3)) > l_9))
    { 
        if (((7UL < 7L) > g_2))
        { 
            int32_t l_17 = 8L;
            l_17 = ((safe_mod_func_uint64_t_u_u(((safe_mod_func_int32_t_s_s(l_17, g_6)) <= g_6), g_10)) && l_17);
        }
        else
        { 
            int8_t l_19 = 0xF9L;
            if (g_2)
                goto lbl_18;
            l_9 = (g_2 | l_19);
        }
        g_29 = (safe_lshift_func_uint8_t_u_u((safe_div_func_int16_t_s_s((+(l_9 = (((safe_mul_func_uint8_t_u_u(((safe_sub_func_uint16_t_u_u((0xFDL > 0x42L), g_10)) > 18446744073709551613UL), 0x8EL)) & (-3L)) < g_10))), g_6)), 1));
        g_30 &= (g_6 , 0xCA0E2C23L);
    }
    else
    { 
        uint64_t l_31 = 0x314D41BD43D9C8C7LL;
        int32_t l_41 = 5L;
        g_32 |= (l_31 >= l_31);
        for (g_10 = (-3); (g_10 > 48); g_10 = safe_add_func_int8_t_s_s(g_10, 1))
        { 
            int32_t l_40 = 0xAB8AC29BL;
            g_35 |= g_6;
            l_41 = (safe_mul_func_uint8_t_u_u(((safe_lshift_func_uint8_t_u_u(((l_40 = (g_30 == g_6)) < g_10), 4)) && l_40), g_35));
            for (l_9 = 0; (l_9 != 15); l_9 = safe_add_func_int64_t_s_s(l_9, 1))
            { 
                int16_t l_54 = 0L;
                int32_t l_55 = 0x6E56995EL;
                l_55 |= (safe_mod_func_uint32_t_u_u(((safe_lshift_func_uint8_t_u_u((safe_rshift_func_uint8_t_u_s((safe_mod_func_int64_t_s_s((safe_add_func_int64_t_s_s(((l_54 == 0UL) <= l_41), 1UL)), 1L)), 6)), g_6)) , 0x0B51ECDEL), 0x4C77A5C6L));
            }
            if (g_32)
                break;
        }
    }
    g_58 |= ((safe_sub_func_int64_t_s_s((((((4294967295UL == g_35) | g_29) < 0x36L) || l_3) == g_2), g_2)) <= g_29);
    return l_3;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_29, "g_29", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    transparent_crc(g_32, "g_32", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    transparent_crc(g_58, "g_58", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
