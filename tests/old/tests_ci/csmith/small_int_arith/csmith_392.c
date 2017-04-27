// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_392.c
#include "csmith.h"


static long __undefined;



static int8_t g_5 = (-7L);
static int32_t g_6 = 0xD035C573L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint32_t l_2 = 0x3A4A9BDBL;
    int32_t l_3 = (-1L);
    int32_t l_4 = 0x01BD97A8L;
    l_4 ^= (l_3 |= l_2);
    l_4 = g_5;
    g_6 = 8L;
    return l_4;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
