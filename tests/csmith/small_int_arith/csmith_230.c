// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_230.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0x55BB2C21L;
static uint32_t g_6 = 1UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint16_t l_5 = 0x7689L;
    int32_t l_7 = 0xCD16652DL;
    --g_2;
    g_6 = l_5;
    l_7 = ((((-4L) > 0x4DFBD6C3L) > l_5) >= 0x443AL);
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
