// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_233.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 0x7CB3L;
static uint16_t g_6 = 1UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint16_t l_11 = 0x2391L;
    int32_t l_12 = (-9L);
    g_2 = 3L;
    for (g_2 = (-27); (g_2 == 29); g_2++)
    { 
        int32_t l_5 = 5L;
        return l_5;
    }
    --g_6;
    l_12 = (safe_mod_func_int16_t_s_s(((((((((g_6 = (g_2 != 0UL)) == 0x2265L) || l_11) , 0x4EL) , g_6) & 0xEDADE0980DB959C4LL) , g_2) >= l_11), g_2));
    return l_12;
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
