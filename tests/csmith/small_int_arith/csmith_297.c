// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_297.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0x2071B18D4081C290LL;
static int8_t g_3 = 7L;
static uint32_t g_4 = 0UL;
static int32_t g_5 = 0L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint64_t l_6 = 1UL;
    g_5 = (g_4 = (g_3 &= g_2));
    return l_6;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
