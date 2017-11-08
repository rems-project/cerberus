// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_462.c
#include "csmith.h"


static long __undefined;



static uint8_t g_3 = 255UL;
static int64_t g_4 = 1L;
static uint32_t g_7 = 4UL;
static int8_t g_13 = 1L;
static uint8_t g_15 = 0x8DL;
static int64_t g_18 = 0xB1B6FD43DDCA2728LL;
static uint32_t g_20 = 0UL;



static const int8_t  func_1(void);




static const int8_t  func_1(void)
{ 
    uint8_t l_2 = 0UL;
    uint32_t l_5 = 0xC9ED9BA0L;
    uint32_t l_10 = 0xC345FE46L;
    uint64_t l_23 = 0xEA14C5530C4E2BF5LL;
    if (l_2)
    { 
        int32_t l_6 = 3L;
        g_4 ^= g_3;
        l_6 = l_5;
    }
    else
    { 
        return g_3;
    }
    if (g_3)
    { 
        int16_t l_14 = (-1L);
        --g_7;
        --l_10;
        --g_15;
    }
    else
    { 
        uint16_t l_19 = 1UL;
        g_18 = l_10;
        l_19 = 0x6E9F0866L;
        ++g_20;
        l_23 = g_13;
    }
    return g_18;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
