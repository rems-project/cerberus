// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_273.c
#include "csmith.h"


static long __undefined;



static int16_t g_6 = 0x62E0L;
static uint64_t g_7 = 0x7F5ED9A924C00011LL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint16_t l_2 = 65535UL;
    int32_t l_3 = (-1L);
    l_3 = (l_2 >= l_2);
    g_7 &= (safe_div_func_uint16_t_u_u((g_6 , l_3), (-3L)));
    return g_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
