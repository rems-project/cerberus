// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_082.c
#include "csmith.h"


static long __undefined;



static int16_t g_7 = 6L;
static int8_t g_8 = (-1L);
static int16_t g_9 = 0L;
static int32_t g_15 = 0x5CF1C946L;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int8_t l_6 = 0x48L;
    int32_t l_14 = (-9L);
    g_8 = (safe_div_func_uint8_t_u_u(((safe_div_func_uint16_t_u_u(((l_6 <= g_7) == 0x3C891C55L), l_6)) <= 0xAA6E6F7FBF2121F9LL), g_7));
    g_9 = 1L;
    l_14 = ((safe_mul_func_uint16_t_u_u(((((safe_rshift_func_uint16_t_u_s(65532UL, g_8)) > g_9) || l_6) , g_7), g_9)) & 0xFA1E1C5AL);
    g_15 &= l_14;
    return g_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
