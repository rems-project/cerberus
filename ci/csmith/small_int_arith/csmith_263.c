// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_263.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 9UL;
static uint32_t g_5 = 0x248C66F5L;
static uint16_t g_12 = 65526UL;
static int16_t g_15 = 1L;
static uint16_t g_16 = 0UL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int16_t l_2 = 0xB7C7L;
    int32_t l_3 = (-8L);
    uint8_t l_10 = 0UL;
    uint64_t l_11 = 0x7249AAED6B65720BLL;
    l_3 = (l_2 = 2L);
    g_5 = g_4;
    g_12 &= ((safe_mul_func_uint8_t_u_u(((((safe_div_func_uint32_t_u_u((2L == l_10), l_11)) == g_5) , 0x266D210EL) >= 0xBD652568L), 0UL)) || (-9L));
    for (l_10 = 0; (l_10 >= 59); l_10++)
    { 
        g_16 = ((g_15 ^= g_12) || 7L);
        return g_16;
    }
    return l_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
