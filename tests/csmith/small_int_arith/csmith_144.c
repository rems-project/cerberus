// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_144.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-3L);
static uint32_t g_10 = 4294967290UL;
static int32_t g_12 = (-4L);
static uint16_t g_13 = 0xA80BL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    for (g_2 = (-23); (g_2 >= 7); g_2 = safe_add_func_uint64_t_u_u(g_2, 1))
    { 
        int8_t l_11 = 0xF1L;
        g_10 = (+((safe_lshift_func_int16_t_s_u((safe_mul_func_uint16_t_u_u(65530UL, 0UL)), g_2)) , 0xB6EC79CFL));
        l_11 = (g_10 <= 0x06887E08A11015AALL);
        --g_13;
    }
    return g_12;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
