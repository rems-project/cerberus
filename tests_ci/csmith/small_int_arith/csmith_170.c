// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_170.c
#include "csmith.h"


static long __undefined;



static uint8_t g_3 = 247UL;
static uint64_t g_4 = 1UL;
static int8_t g_7 = (-7L);
static uint32_t g_8 = 4294967295UL;
static uint64_t g_14 = 9UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int8_t l_5 = 0x28L;
    int32_t l_6 = 0xAA0D7227L;
    g_4 = (+(0L >= g_3));
    g_7 = ((l_6 &= ((8UL || g_4) , l_5)) && l_6);
    --g_8;
    g_14 = (((((~((safe_lshift_func_int16_t_s_u((((-5L) > l_6) && 0xA017779A7B445ACELL), l_5)) || l_6)) == l_6) >= g_3) | l_6) , g_4);
    return l_6;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
