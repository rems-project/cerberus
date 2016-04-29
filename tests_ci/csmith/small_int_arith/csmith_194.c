// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_194.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 4294967292UL;
static uint8_t g_11 = 255UL;
static uint32_t g_14 = 0x3B372BA2L;
static int8_t g_36 = 0L;
static int8_t g_38 = 9L;
static uint32_t g_51 = 0x0D8AC507L;
static uint32_t g_52 = 0x9BEC7A42L;
static int32_t g_57 = 0xF618E188L;
static int32_t g_58 = 0x7F726845L;
static uint8_t g_61 = 0xF0L;
static uint32_t g_65 = 0xD8D7CD14L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_50 = 0x16511C25L;
    int32_t l_60 = 0xABE3335AL;
    if (g_2)
    { 
        int64_t l_5 = 0L;
        uint8_t l_6 = 0x11L;
        uint16_t l_9 = 0xF5AFL;
        int32_t l_15 = 0x2BDB979CL;
        for (g_2 = (-17); (g_2 < 60); g_2 = safe_add_func_int8_t_s_s(g_2, 2))
        { 
            l_6 = l_5;
            l_9 = ((safe_div_func_int32_t_s_s(0xFC371865L, g_2)) < 0xD416DB6DL);
            g_11 = ((~0xA522L) , 0xD42CA8CDL);
            l_15 = (safe_rshift_func_uint16_t_u_u(g_11, g_14));
        }
    }
    else
    { 
        uint16_t l_20 = 65535UL;
        int32_t l_37 = 0x4067BC62L;
        uint32_t l_40 = 0UL;
        uint32_t l_44 = 0UL;
        for (g_14 = 0; (g_14 > 44); ++g_14)
        { 
            uint8_t l_27 = 0x0EL;
            int32_t l_43 = 1L;
            int8_t l_56 = 0L;
            int32_t l_59 = 0x592E0C80L;
            int32_t l_64 = (-3L);
            if ((safe_div_func_int32_t_s_s(g_14, l_20)))
            { 
                int8_t l_26 = (-1L);
                int32_t l_39 = 0L;
                l_27 &= ((~(safe_lshift_func_uint16_t_u_s((safe_sub_func_uint8_t_u_u((4294967295UL && l_26), g_2)), 0))) , g_11);
                g_36 ^= (((safe_add_func_uint8_t_u_u((safe_rshift_func_int8_t_s_u((safe_mul_func_int16_t_s_s((safe_rshift_func_uint8_t_u_u(g_14, 6)), g_14)), g_14)), 0xA2L)) && l_20) && g_14);
                if (g_36)
                { 
                    return g_2;
                }
                else
                { 
                    l_40--;
                }
            }
            else
            { 
                int32_t l_49 = 0xAF3922CBL;
                g_51 = ((l_44--) == (safe_sub_func_int64_t_s_s((l_49 , l_50), g_36)));
                --g_52;
                l_56 |= ((l_50 = (+g_52)) ^ 2L);
                g_57 = 0xFDAF0DB1L;
            }
            g_61--;
            g_57 = (-8L);
            g_65++;
        }
        g_57 = l_50;
    }
    return l_50;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_36, "g_36", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    transparent_crc(g_51, "g_51", print_hash_value);
    transparent_crc(g_52, "g_52", print_hash_value);
    transparent_crc(g_57, "g_57", print_hash_value);
    transparent_crc(g_58, "g_58", print_hash_value);
    transparent_crc(g_61, "g_61", print_hash_value);
    transparent_crc(g_65, "g_65", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
