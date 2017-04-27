// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_335.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xDF75DCECL;
static int64_t g_12 = 0x023DCDF5EF889A27LL;
static int32_t g_13 = (-1L);
static int8_t g_15 = (-6L);
static int8_t g_16 = 0xF4L;
static uint32_t g_20 = 0xEB2FC257L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int16_t l_11 = 0xF44CL;
    int32_t l_14 = (-1L);
    int32_t l_17 = 1L;
    int32_t l_19 = 0L;
    uint16_t l_23 = 65531UL;
    if (g_2)
    { 
        uint32_t l_5 = 8UL;
        uint8_t l_10 = 7UL;
        int32_t l_18 = 0x54E3F157L;
        for (g_2 = 0; (g_2 != 6); g_2++)
        { 
            ++l_5;
        }
        l_11 = ((((safe_mod_func_int16_t_s_s(((l_5 == 0x7AL) >= g_2), l_5)) < g_2) == 1UL) , l_10);
        g_20--;
        ++l_23;
    }
    else
    { 
        return g_2;
    }
    return l_14;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
