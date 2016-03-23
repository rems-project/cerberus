// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_303.c
#include "csmith.h"


static long __undefined;



static int64_t g_5 = 0xEBB6748F69F7FD1ELL;
static uint64_t g_9 = 18446744073709551615UL;
static int16_t g_13 = 1L;
static int16_t g_15 = 0x4392L;
static uint16_t g_16 = 0xF609L;
static int32_t g_20 = 0L;
static uint32_t g_25 = 4294967295UL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint8_t l_4 = 0xCBL;
    int32_t l_6 = 0x43046B6EL;
    int32_t l_14 = 1L;
    int64_t l_19 = (-6L);
    l_6 ^= (safe_div_func_int8_t_s_s((l_4 || g_5), g_5));
    if (g_5)
    { 
        int32_t l_10 = 0L;
        for (l_6 = 0; (l_6 > (-4)); --l_6)
        { 
            int16_t l_11 = 7L;
            int32_t l_12 = 0x9B69B2E4L;
            g_13 = ((l_12 = (((g_9 = g_5) == l_10) && l_11)) ^ l_4);
            l_14 = (l_12 = ((g_13 && (-9L)) == l_6));
            ++g_16;
            if (g_9)
                continue;
        }
        g_20 &= (l_19 = 3L);
    }
    else
    { 
        uint8_t l_28 = 0xB3L;
        for (g_9 = (-29); (g_9 >= 29); ++g_9)
        { 
            int32_t l_23 = 8L;
            int32_t l_24 = 0xAD901516L;
            --g_25;
        }
        l_28 = 0x0F888C55L;
    }
    g_20 &= l_14;
    return g_9;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
