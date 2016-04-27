// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o gen/csmith_04.c
#include "csmith.h"


static long __undefined;



static int32_t g_5 = (-4L);



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint32_t l_4 = 0UL;
    int32_t l_6 = 0x8815CBCEL;
    l_6 = (safe_lshift_func_int16_t_s_u(((((l_4 & g_5) != g_5) >= 255UL) , l_4), l_4));
    return g_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
