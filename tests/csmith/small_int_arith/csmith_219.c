// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_219.c
#include "csmith.h"


static long __undefined;



static int64_t g_3 = 1L;
static uint64_t g_5 = 18446744073709551612UL;
static uint32_t g_10 = 0x4D9EDBDAL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int16_t l_2 = 3L;
    int32_t l_4 = 0xDC4B4E12L;
    if (l_2)
    { 
        g_5++;
    }
    else
    { 
        l_4 = (safe_add_func_uint32_t_u_u(g_5, 0x3921DED6L));
    }
    g_10 = g_5;
    return g_3;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
