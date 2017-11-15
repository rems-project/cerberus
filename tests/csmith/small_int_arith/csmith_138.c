// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_138.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xE1757117L;
static int8_t g_5 = (-7L);
static uint8_t g_14 = 0x8AL;
static int64_t g_16 = (-7L);
static uint32_t g_24 = 4UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint8_t l_6 = 255UL;
    uint16_t l_27 = 0xED6CL;
    int16_t l_32 = (-1L);
    for (g_2 = 0; (g_2 > (-20)); g_2 = safe_sub_func_int32_t_s_s(g_2, 5))
    { 
        uint64_t l_15 = 0UL;
        int32_t l_19 = 0L;
        int32_t l_22 = 0x0547507AL;
        g_5 = g_2;
        if (l_6)
        { 
            uint16_t l_7 = 5UL;
            int32_t l_8 = 0xE64F1479L;
            l_8 &= l_7;
            g_16 = ((+((safe_sub_func_int32_t_s_s(((safe_div_func_int16_t_s_s((g_14 = ((((1UL > 0xE7L) ^ 1UL) == g_5) & 0UL)), g_2)) & g_2), l_15)) & g_5)) && g_14);
            l_19 = ((safe_mod_func_uint8_t_u_u(0x7FL, l_8)) ^ 0x8A01L);
            for (l_19 = 1; (l_19 < (-23)); --l_19)
            { 
                int32_t l_23 = 0xE8F08877L;
                uint32_t l_30 = 7UL;
                l_22 = l_15;
                --g_24;
                l_27 &= g_16;
                l_30 |= ((safe_mul_func_int16_t_s_s(g_5, g_5)) || l_23);
            }
        }
        else
        { 
            int16_t l_31 = 8L;
            return l_31;
        }
        l_32 = g_5;
    }
    return g_16;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
