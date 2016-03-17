// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_332.c
#include "csmith.h"


static long __undefined;



static int64_t g_3 = 0x6951AD386CCE57BFLL;
static uint64_t g_4 = 0x6E5C7A00F47A6DEELL;
static uint32_t g_6 = 0xBF0DDD9CL;
static int32_t g_10 = 1L;
static int16_t g_15 = 0x9B7DL;
static int32_t g_39 = 0L;
static int8_t g_47 = 0x8CL;
static uint16_t g_48 = 0x6BFEL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint32_t l_2 = 4294967295UL;
    int32_t l_9 = 0xA017779AL;
    int32_t l_11 = 0xC299E885L;
    int32_t l_14 = (-7L);
    uint8_t l_19 = 0x71L;
lbl_40:
    if ((g_4 ^= (l_2 <= g_3)))
    { 
        int64_t l_5 = 0xB9849B76EEA53061LL;
        int32_t l_12 = 0xAB3CF813L;
        if (((((8L >= g_4) == g_4) <= 0x047C4D14L) | g_4))
        { 
            g_6 = (l_5 = l_2);
            if (l_2)
                goto lbl_40;
        }
        else
        { 
            uint8_t l_16 = 3UL;
            int32_t l_24 = (-10L);
            int32_t l_36 = 0xBF12959AL;
            for (g_3 = 0; (g_3 != 20); g_3 = safe_add_func_int32_t_s_s(g_3, 8))
            { 
                int64_t l_13 = 0x3D5943E2F7C629C4LL;
                l_16--;
                l_19--;
                l_24 &= ((((safe_mod_func_int16_t_s_s(g_3, 0xC509L)) == g_3) ^ g_10) <= l_5);
                if (g_10)
                    continue;
            }
            for (l_24 = (-7); (l_24 <= (-7)); ++l_24)
            { 
                uint16_t l_35 = 0x6C84L;
                l_12 = (((safe_add_func_int32_t_s_s((!(safe_div_func_int32_t_s_s((safe_sub_func_int8_t_s_s(g_10, 0x3EL)), l_24))), 4294967295UL)) , g_3) ^ g_3);
                l_36 = ((g_3 ^= (l_35 |= (safe_unary_minus_func_uint32_t_u(g_6)))) > (-8L));
            }
        }
    }
    else
    { 
        int8_t l_37 = 0xD3L;
        if (l_37)
        { 
            uint32_t l_38 = 18446744073709551611UL;
            g_39 = (((((g_10 <= (-1L)) == 1UL) , l_38) > l_38) == g_6);
            return l_38;
        }
        else
        { 
            return l_14;
        }
    }
    l_14 = ((safe_sub_func_int8_t_s_s(((safe_sub_func_int8_t_s_s((g_48 |= (((((g_47 = (safe_add_func_uint64_t_u_u(g_6, g_3))) & g_3) == g_6) ^ g_3) || g_6)), 0x74L)) & 2L), g_15)) , 1L);
    return l_19;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_39, "g_39", print_hash_value);
    transparent_crc(g_47, "g_47", print_hash_value);
    transparent_crc(g_48, "g_48", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
