// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_341.c
#include "csmith.h"


static long __undefined;



static uint32_t g_12 = 0xFF40FC02L;
static int64_t g_22 = 0x6C84902314AF12A8LL;
static uint64_t g_24 = 18446744073709551607UL;
static uint8_t g_27 = 0x5CL;
static uint64_t g_32 = 0xB39D20578CCA6991LL;
static uint8_t g_36 = 0x9AL;
static uint32_t g_40 = 7UL;
static int16_t g_48 = 0x5465L;
static int16_t g_52 = (-1L);



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint8_t l_13 = 0xE7L;
    int32_t l_41 = (-1L);
    if (((safe_div_func_uint16_t_u_u((safe_rshift_func_uint16_t_u_u(((safe_lshift_func_int8_t_s_s((safe_rshift_func_uint8_t_u_s((safe_div_func_uint64_t_u_u(g_12, g_12)), 6)), g_12)) , l_13), 4)), g_12)) , 0x568BE135L))
    { 
        uint64_t l_19 = 0x4C3F4F88039D6B9CLL;
        int32_t l_31 = 1L;
        int32_t l_39 = 1L;
        for (l_13 = (-7); (l_13 > 53); l_13++)
        { 
            uint32_t l_18 = 0x9161D594L;
            int32_t l_23 = 0x5EBEC5ECL;
            if (((safe_mul_func_int16_t_s_s(l_18, 0x7EA0L)) , l_19))
            { 
                int64_t l_30 = 8L;
                for (g_12 = 0; (g_12 == 30); g_12 = safe_add_func_uint16_t_u_u(g_12, 4))
                { 
                    ++g_24;
                }
                g_27++;
                g_32++;
            }
            else
            { 
                int8_t l_35 = 7L;
                g_36 = l_35;
            }
            g_40 = (((((((((((safe_rshift_func_int8_t_s_s(g_27, l_13)) == l_39) && (-1L)) <= 0x8792L) || g_27) > g_22) , l_23) , l_13) == g_32) < g_36) <= g_24);
        }
        l_41 = 4L;
        l_31 = (((safe_mod_func_int64_t_s_s((safe_rshift_func_int8_t_s_s((g_48 = (((safe_lshift_func_int16_t_s_u((((l_41 , 0x5BDDDD5D57D38C46LL) ^ 0x8E9D28BC130268D9LL) | g_40), 11)) ^ l_39) , l_39)), l_31)), 0x6D70783DB47DC462LL)) | 1L) & l_13);
    }
    else
    { 
        uint16_t l_49 = 9UL;
        l_49--;
    }
    g_52 = (((0xA528L > l_13) >= g_24) & l_13);
    l_41 = g_22;
    return g_32;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    transparent_crc(g_32, "g_32", print_hash_value);
    transparent_crc(g_36, "g_36", print_hash_value);
    transparent_crc(g_40, "g_40", print_hash_value);
    transparent_crc(g_48, "g_48", print_hash_value);
    transparent_crc(g_52, "g_52", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
