// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_066.c
#include "csmith.h"


static long __undefined;



static uint16_t g_3 = 1UL;
static int8_t g_9 = 0xFDL;
static uint64_t g_11 = 0x7E3B6F9B6917AB6DLL;
static int32_t g_14 = 0x863718BDL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint32_t l_2 = 1UL;
    int32_t l_5 = 0x6310FECAL;
    int16_t l_6 = 5L;
    int32_t l_7 = 0xAEF6E229L;
    int32_t l_8 = 0xECF7921EL;
    int32_t l_10 = (-1L);
    if (((l_2 ^ (-8L)) < 0xAC70L))
    { 
        g_3 = l_2;
    }
    else
    { 
        int32_t l_4 = 0xABFC3938L;
        l_5 &= (((-7L) != l_4) >= l_4);
    }
    l_5 = g_3;
    g_11++;
    l_7 = l_10;
    return g_14;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
