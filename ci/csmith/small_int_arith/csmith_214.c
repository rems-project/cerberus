// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_214.c
#include "csmith.h"


static long __undefined;



static uint32_t g_7 = 3UL;
static int32_t g_9 = 0L;
static int32_t g_12 = (-10L);
static uint64_t g_13 = 0x7C2C9EBF495E3B37LL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint64_t l_2 = 0x2E0CF5720E83C773LL;
    int32_t l_8 = 5L;
    uint32_t l_22 = 4294967293UL;
    if (l_2)
    { 
        uint32_t l_6 = 4294967295UL;
        int16_t l_10 = 0x3A92L;
        for (l_2 = 2; (l_2 != 32); l_2++)
        { 
            uint8_t l_5 = 1UL;
            int32_t l_11 = 0xDA2AE7B7L;
            l_8 ^= (((l_5 , l_6) , (-1L)) | g_7);
            l_10 = (g_9 = l_5);
            --g_13;
            l_11 |= (safe_unary_minus_func_uint64_t_u((0UL | g_13)));
        }
    }
    else
    { 
        int8_t l_21 = 7L;
        for (g_7 = 15; (g_7 != 6); g_7--)
        { 
            for (g_9 = 0; (g_9 < 15); g_9++)
            { 
                return g_13;
            }
        }
        --l_22;
    }
    l_8 = ((((-1L) > 1UL) == g_12) != l_22);
    return l_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
