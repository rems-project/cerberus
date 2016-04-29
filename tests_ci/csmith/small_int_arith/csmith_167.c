// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_167.c
#include "csmith.h"


static long __undefined;



static int16_t g_3 = 1L;
static int16_t g_4 = 0xAFE0L;
static int64_t g_6 = (-5L);
static int8_t g_7 = 2L;
static int32_t g_8 = 0x5A5EFA20L;
static uint16_t g_9 = 65527UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int32_t l_2 = 3L;
    int32_t l_5 = 0xA888ADAEL;
    l_5 = ((++g_9) , g_6);
    return l_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
