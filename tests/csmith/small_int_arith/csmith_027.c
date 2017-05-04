// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_027.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x24039B64L;
static uint64_t g_3 = 0x743D837BC75286E8LL;
static uint32_t g_11 = 0xCFD1F2E9L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int16_t l_8 = 0xE307L;
    int64_t l_9 = (-1L);
    ++g_3;
    l_9 = ((safe_add_func_int16_t_s_s(l_8, 0xCA98L)) > l_8);
    g_11 = (+1UL);
    return g_3;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
