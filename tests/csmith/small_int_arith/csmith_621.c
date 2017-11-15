// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_621.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2 = 0xEDF1FEBAEEF20FE6LL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint8_t l_3 = 0x7AL;
    uint16_t l_4 = 65529UL;
    uint64_t l_8 = 0UL;
    int32_t l_10 = (-4L);
    g_2 = 1L;
    if (l_3)
    { 
        uint32_t l_5 = 18446744073709551614UL;
        l_4 = g_2;
        ++l_5;
    }
    else
    { 
        int32_t l_9 = 0L;
        l_8 = g_2;
        l_9 ^= (-1L);
    }
    l_10 = 0x8373B2C5L;
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
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
