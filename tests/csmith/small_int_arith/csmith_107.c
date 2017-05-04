// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_107.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xF5540D7FL;
static uint8_t g_9 = 0x5EL;
static uint32_t g_10 = 4294967295UL;
static int8_t g_11 = 0x13L;
static uint16_t g_30 = 0xA9A9L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int64_t l_8 = 9L;
    int32_t l_22 = 0L;
    int32_t l_23 = 0x758B39D2L;
    int32_t l_24 = (-5L);
    int32_t l_25 = 0xB79DC866L;
    int32_t l_26 = 0x2A6F9A4DL;
    int32_t l_27 = 0x5FCB4448L;
    int32_t l_28 = 0x7F13BCF5L;
    int32_t l_29 = (-1L);
    uint64_t l_33 = 0x8670FC24489BE67ELL;
    for (g_2 = 12; (g_2 < (-17)); g_2 = safe_sub_func_int8_t_s_s(g_2, 2))
    { 
        uint8_t l_7 = 0x51L;
        if (g_2)
            break;
        if (g_2)
            continue;
        g_11 = (g_10 = (safe_lshift_func_int16_t_s_u(((g_9 = ((l_7 || l_8) <= 0x0E704F3D4E677B56LL)) >= g_2), 4)));
    }
    for (g_2 = 20; (g_2 > (-21)); g_2 = safe_sub_func_int16_t_s_s(g_2, 8))
    { 
        uint16_t l_18 = 0UL;
        int32_t l_19 = 0x81ECA6C8L;
        l_19 |= (safe_sub_func_uint16_t_u_u((safe_sub_func_int8_t_s_s(((l_18 = (-1L)) < l_8), g_10)), 0UL));
        l_22 = ((safe_lshift_func_int8_t_s_u((g_10 ^ g_2), 1)) , g_9);
        if (l_8)
            break;
    }
    g_30--;
    return l_33;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
