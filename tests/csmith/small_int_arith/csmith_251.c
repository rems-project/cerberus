// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_251.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 18446744073709551615UL;
static uint8_t g_4 = 0xA8L;
static int64_t g_10 = (-1L);
static int16_t g_11 = 0x3700L;
static uint32_t g_14 = 4UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_3 = 0x82A1836CL;
    int32_t l_7 = 0x1D2250DBL;
lbl_15:
    g_4 = (((g_2 ^ g_2) , l_3) , l_3);
    l_7 = (safe_mul_func_uint8_t_u_u(g_4, l_3));
    g_11 &= ((((g_10 = ((safe_rshift_func_int8_t_s_s((0x05732AA61FC2DA8ALL && g_2), 1)) , l_7)) == 0x5FA3L) && l_3) == (-9L));
    for (g_2 = 0; (g_2 == 43); g_2++)
    { 
        g_14 = (g_11 , g_11);
        if (g_11)
            goto lbl_15;
    }
    return g_14;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
