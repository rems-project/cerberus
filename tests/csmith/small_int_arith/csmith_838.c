// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_838.c
#include "csmith.h"


static long __undefined;



static int16_t g_4 = 0xDD03L;
static uint16_t g_5 = 0xE6F7L;
static uint64_t g_6 = 0xC1188E17B844A754LL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int8_t l_2 = 0xBAL;
    int32_t l_3 = 0xE53D8DA8L;
    l_3 = l_2;
    l_3 &= g_4;
    if (l_2)
    { 
        g_5 ^= 0x1C5534BFL;
    }
    else
    { 
        int32_t l_7 = (-7L);
        g_6 = l_3;
        l_3 = 0xF415D724L;
        l_3 = l_7;
        l_3 &= g_4;
    }
    for (g_5 = 0; (g_5 > 54); g_5++)
    { 
        int64_t l_10 = (-10L);
        l_3 = l_10;
        if (g_4)
            continue;
    }
    return l_3;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
