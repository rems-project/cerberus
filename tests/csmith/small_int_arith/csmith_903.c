// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_903.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 1L;
static int32_t g_4 = (-1L);
static int8_t g_6 = (-10L);
static int8_t g_9 = 1L;
static uint64_t g_13 = 0x7F451D52AA0A5DECLL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int32_t l_2 = (-1L);
    int32_t l_5 = (-8L);
    int32_t l_7 = 9L;
    int32_t l_8 = 1L;
    int32_t l_17 = (-2L);
    g_3 = l_2;
    if (g_3)
    { 
        uint8_t l_10 = 0xF6L;
        g_4 &= g_3;
        ++l_10;
        g_3 &= 0x4CE55459L;
    }
    else
    { 
        uint8_t l_16 = 3UL;
        --g_13;
        l_16 |= g_6;
    }
    g_3 ^= l_17;
    return l_8;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
