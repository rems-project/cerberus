// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_554.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0x2FE2236432A27689LL;
static int8_t g_4 = 0x67L;
static uint32_t g_7 = 1UL;
static uint8_t g_8 = 0xD5L;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint64_t l_5 = 0xBD6C3F0BC5021C3ALL;
    int32_t l_9 = 0x2B534DE6L;
    g_2 = 0xB9B55BB2L;
    if (g_2)
    { 
        uint32_t l_3 = 4UL;
        g_4 = l_3;
    }
    else
    { 
        uint8_t l_6 = 3UL;
        l_6 ^= l_5;
        g_7 = 0x46DDCD16L;
        g_8 = g_2;
    }
    l_9 ^= g_8;
    return g_2;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
