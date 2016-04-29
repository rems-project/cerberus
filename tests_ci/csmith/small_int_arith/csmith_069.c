// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_069.c
#include "csmith.h"


static long __undefined;



static uint64_t g_4 = 0xC2DB22124F84B811LL;
static uint32_t g_6 = 18446744073709551615UL;
static uint8_t g_7 = 0x3BL;
static uint32_t g_8 = 7UL;
static uint32_t g_11 = 0x8591B68DL;
static int64_t g_18 = 0x3E52509E71B35D56LL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int32_t l_5 = 1L;
    int32_t l_9 = 0L;
    int32_t l_10 = 0xC88EB987L;
    g_8 ^= (g_7 = (safe_sub_func_uint8_t_u_u((g_6 &= (g_4 >= l_5)), l_5)));
    ++g_11;
    l_9 = (l_5 < l_5);
    g_18 = (safe_rshift_func_int16_t_s_u((safe_mul_func_uint16_t_u_u(l_5, 0xEDF6L)), g_6));
    return g_6;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
