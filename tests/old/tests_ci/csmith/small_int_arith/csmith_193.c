// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_193.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x313DD33AL;
static int32_t g_5 = 0x8C9F3690L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int64_t l_17 = (-1L);
    for (g_2 = 0; (g_2 <= 28); g_2++)
    { 
        int16_t l_8 = 0x35E4L;
        uint16_t l_9 = 0xA94BL;
        int32_t l_10 = 8L;
        g_5 = 0xE01BD97AL;
        l_10 &= (l_9 = (safe_rshift_func_uint16_t_u_s(1UL, l_8)));
        for (l_8 = 0; (l_8 == 29); ++l_8)
        { 
            uint32_t l_15 = 0xA0A5DEC4L;
            int32_t l_16 = 0L;
            l_16 &= (safe_mul_func_int16_t_s_s(g_2, l_15));
            return l_17;
        }
    }
    return l_17;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
