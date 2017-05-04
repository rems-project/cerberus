// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_252.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0xEC2DB22124F84B81LL;
static int64_t g_5 = 0x3D42374B1B055CC2LL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_3 = 2L;
    int32_t l_4 = 1L;
    g_5 &= ((l_3 = ((g_2 >= l_3) <= g_2)) , l_4);
    return g_2;
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
