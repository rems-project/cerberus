// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_089.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = 1L;
static uint64_t g_3 = 18446744073709551614UL;
static uint64_t g_5 = 18446744073709551608UL;
static int8_t g_6 = 0x81L;
static uint8_t g_10 = 1UL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint64_t l_4 = 18446744073709551606UL;
    int32_t l_7 = (-3L);
    int32_t l_8 = 0xED1AD67AL;
    int32_t l_9 = 0x590F0234L;
    g_3 = g_2;
    g_5 = (l_4 < 0x02E31D83L);
    g_10++;
    return l_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
