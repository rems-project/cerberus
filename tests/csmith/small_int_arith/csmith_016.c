// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_016.c
#include "csmith.h"


static long __undefined;



static int64_t g_7 = 0x5B2906C902DAFBBDLL;
static uint8_t g_10 = 9UL;
static int8_t g_12 = 1L;
static uint32_t g_15 = 0x27A4129BL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint8_t l_6 = 255UL;
    int8_t l_8 = (-10L);
    int32_t l_9 = 0x9934B0B4L;
    int32_t l_11 = 0x7E80D68FL;
    int32_t l_13 = 0x7C7AB89BL;
    int32_t l_14 = 0xB168F928L;
    g_10 = (((safe_lshift_func_int16_t_s_s(((((safe_mod_func_int8_t_s_s((l_6 | 0xD8F8F576L), (-3L))) & l_6) > g_7) & g_7), l_8)) < g_7) | l_9);
    ++g_15;
    return g_10;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
