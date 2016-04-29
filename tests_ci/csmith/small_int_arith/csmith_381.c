// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_381.c
#include "csmith.h"


static long __undefined;



static int16_t g_4 = 0x0E60L;
static uint16_t g_5 = 0UL;
static int32_t g_6 = (-1L);



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_12 = 9L;
    int32_t l_13 = 0x790E8648L;
    g_6 = (g_5 |= ((safe_mul_func_uint8_t_u_u((g_4 != g_4), g_4)) & 3UL));
    g_6 = ((safe_div_func_uint16_t_u_u((+((l_13 ^= ((safe_mul_func_uint16_t_u_u(g_4, g_4)) == l_12)) , l_12)), l_12)) ^ 0L);
    g_6 ^= g_4;
    g_6 = (1L ^ g_6);
    return g_4;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
