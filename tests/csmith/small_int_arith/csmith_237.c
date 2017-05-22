// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_237.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-1L);
static int8_t g_5 = 0xC2L;
static uint8_t g_6 = 0xF8L;
static int32_t g_12 = 0L;
static int32_t g_22 = 0xB3E713E1L;
static int32_t g_23 = 0x2509E71BL;
static uint8_t g_26 = 248UL;
static uint32_t g_34 = 3UL;
static uint64_t g_38 = 0x309AB83EB61943ECLL;
static int32_t g_41 = 0L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint32_t l_13 = 18446744073709551615UL;
    uint8_t l_19 = 254UL;
    int32_t l_20 = (-4L);
    int16_t l_33 = 0xAA23L;
    int32_t l_37 = 0x0DCEE052L;
    for (g_2 = (-17); (g_2 > 3); ++g_2)
    { 
        int16_t l_18 = 0xE21AL;
        int32_t l_21 = 0x75158018L;
        int32_t l_24 = (-1L);
        int32_t l_25 = 0L;
        --g_6;
        for (g_6 = 0; (g_6 >= 1); g_6++)
        { 
            int32_t l_11 = 0x09978F3CL;
            ++l_13;
            if (g_12)
                continue;
        }
        l_20 = ((safe_sub_func_int32_t_s_s((l_18 <= 0xB6L), l_13)) ^ l_19);
        g_26--;
    }
    g_23 = (safe_add_func_uint64_t_u_u(((safe_sub_func_int16_t_s_s((g_26 != (-8L)), 0x80C6L)) , l_13), g_26));
    ++g_34;
    g_23 = ((g_41 ^= (g_38++)) > ((1L | l_13) & l_19));
    return l_13;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_34, "g_34", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    transparent_crc(g_41, "g_41", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
