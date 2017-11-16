// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_515.c
#include "csmith.h"


static long __undefined;



static uint8_t g_3 = 249UL;
static uint16_t g_4 = 0xF25CL;
static int32_t g_10 = 0x7E08A110L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint8_t l_2 = 255UL;
    int32_t l_9 = 0x673292C5L;
    uint32_t l_11 = 0UL;
    l_2 = (-5L);
    if (g_3)
    { 
        return l_2;
    }
    else
    { 
        --g_4;
    }
    for (l_2 = 0; (l_2 <= 13); l_2 = safe_add_func_int64_t_s_s(l_2, 8))
    { 
        g_10 ^= l_9;
        return l_11;
    }
    return g_10;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
