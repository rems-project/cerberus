// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_057.c
#include "csmith.h"


static long __undefined;



static int16_t g_3 = (-3L);



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_2 = 0x31E42A43L;
    g_3 = (((l_2 != l_2) == 0x1AL) <= 0L);
    for (l_2 = 0; (l_2 <= 17); ++l_2)
    { 
        int32_t l_6 = 0x416DB6D0L;
        return l_6;
    }
    return g_3;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
