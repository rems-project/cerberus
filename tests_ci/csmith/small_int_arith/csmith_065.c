// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_065.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0x6BDDE0BCD8C45CDBLL;
static uint16_t g_8 = 8UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_3 = (-1L);
    int32_t l_4 = 0x5816210BL;
    int32_t l_5 = (-3L);
    int32_t l_6 = 1L;
    int32_t l_7 = 0x0585B7F3L;
    uint16_t l_11 = 1UL;
    --g_8;
    return l_11;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
