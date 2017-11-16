// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_080.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = (-1L);
static uint32_t g_3 = 0x9B2CFB63L;
static int8_t g_4 = (-1L);
static int32_t g_6 = 7L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_7 = (-1L);
    if ((g_3 = (g_2 < (-1L))))
    { 
        uint64_t l_5 = 0xC04CCB63E8E1B881LL;
        g_4 = (g_3 && (-9L));
        l_7 = (g_6 = l_5);
    }
    else
    { 
        uint8_t l_8 = 0x8FL;
        int32_t l_9 = 0xFFCF33F2L;
        l_9 ^= ((g_2 , l_8) ^ 0xFCE2L);
    }
    return g_3;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
