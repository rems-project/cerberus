// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_313.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x60477862L;
static uint32_t g_8 = 2UL;
static uint8_t g_11 = 0xBFL;
static int16_t g_19 = 0xC0C8L;
static int32_t g_21 = 0xA14A9C79L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint16_t l_9 = 65529UL;
    int32_t l_10 = 0x2DD78F4FL;
    int32_t l_12 = 0x509CB0BEL;
    uint32_t l_20 = 0UL;
    uint8_t l_25 = 0xB5L;
    for (g_2 = 0; (g_2 == 23); g_2 = safe_add_func_int8_t_s_s(g_2, 8))
    { 
        int8_t l_7 = 0L;
        g_8 = ((safe_rshift_func_int8_t_s_u((g_2 & 0x08974B666A756A33LL), l_7)) , l_7);
        l_12 ^= ((((g_11 = (l_10 ^= ((l_7 <= g_2) == l_9))) >= l_9) >= 0xB2C41AC3L) ^ g_8);
        l_12 = (g_21 |= ((safe_rshift_func_uint16_t_u_u(((((((safe_mul_func_uint16_t_u_u((g_19 = (safe_lshift_func_uint16_t_u_u((l_7 , g_8), l_12))), 0x1883L)) >= g_8) , l_12) , g_11) | g_8) != l_7), l_20)) == g_11));
        l_12 ^= (+(safe_mul_func_uint8_t_u_u(l_7, l_20)));
    }
    g_2 = ((((((l_20 == g_19) > l_10) == l_25) & 6L) , g_21) | 65535UL);
    return l_12;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
