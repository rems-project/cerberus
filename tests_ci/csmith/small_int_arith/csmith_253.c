// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_253.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0x76AABECBL;
static uint32_t g_4 = 18446744073709551615UL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint16_t l_3 = 0xE8C9L;
    int32_t l_5 = 0x5E4B7834L;
    g_4 = ((g_2 && l_3) , g_2);
    l_5 &= (g_2 <= g_4);
    for (g_2 = 0; (g_2 > 22); g_2++)
    { 
        return l_3;
    }
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
