// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_958.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0xC213532FL;
static uint16_t g_4 = 0x2526L;



static int8_t  func_1(void);
static int32_t  func_7(int8_t  p_8, int32_t  p_9, int32_t  p_10);




static int8_t  func_1(void)
{ 
    uint8_t l_3 = 251UL;
    int32_t l_20 = 7L;
    g_2 = (-9L);
    g_4 = l_3;
    for (l_3 = (-11); (l_3 <= 31); l_3++)
    { 
        int32_t l_13 = 0x7ECC2443L;
        uint32_t l_14 = 0x652D0DA0L;
        int16_t l_15 = 3L;
        int32_t l_21 = 0L;
        uint64_t l_23 = 0xFFDEABFD090D790FLL;
        l_20 = func_7((safe_sub_func_int8_t_s_s((l_13 |= 0x23L), l_14)), l_15, l_3);
        l_21 = 0x21A07835L;
        l_20 = (!(l_23 &= (g_4 && l_15)));
    }
    return l_3;
}



static int32_t  func_7(int8_t  p_8, int32_t  p_9, int32_t  p_10)
{ 
    uint16_t l_16 = 0x2F88L;
    const uint8_t l_18 = 0x8CL;
    int32_t l_19 = 0xDC9FE9A5L;
    l_16 ^= ((0x534DE6F885EA6EDALL & 18446744073709551615UL) < 0x28ACE4B0AD8EA5F3LL);
    if ((((!((l_16 || g_4) > p_10)) > l_18) && p_8))
    { 
        return l_18;
    }
    else
    { 
        l_19 = ((((p_9 >= p_10) != p_9) == g_2) & l_16);
        return l_19;
    }
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
