// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_020.c
#include "csmith.h"


static long __undefined;



static int16_t g_5 = (-5L);
static int16_t g_6 = 1L;
static uint16_t g_7 = 0x66A7L;
static uint32_t g_8 = 0UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint32_t l_4 = 0xF57A7C20L;
    g_7 = ((g_6 = (safe_div_func_uint16_t_u_u(l_4, g_5))) , g_5);
    g_8 = (l_4 && g_7);
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
