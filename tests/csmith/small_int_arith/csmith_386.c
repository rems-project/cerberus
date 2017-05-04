// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_386.c
#include "csmith.h"


static long __undefined;



static int64_t g_4 = (-1L);
static uint32_t g_9 = 0UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint32_t l_5 = 18446744073709551606UL;
    int32_t l_6 = 0x72226312L;
    l_6 = ((safe_rshift_func_int16_t_s_u(g_4, g_4)) | l_5);
    g_9 = ((safe_mul_func_int16_t_s_s(g_4, 0x6C51L)) & l_5);
    return g_9;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
