// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_239.c
#include "csmith.h"


static long __undefined;



static uint8_t g_3 = 0x96L;
static int32_t g_5 = 5L;
static uint32_t g_7 = 0UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int16_t l_2 = (-4L);
    int32_t l_4 = 0x649F6D4AL;
    int32_t l_6 = 0xC8F0D071L;
    g_3 = (((((l_2 != l_2) & l_2) <= 0x7F5ED9A924C00011LL) < 65534UL) & l_2);
    g_7--;
    return l_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
