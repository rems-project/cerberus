// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_682.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 1L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint32_t l_3 = 0x838A1F94L;
    int32_t l_4 = (-2L);
    l_3 = g_2;
    l_4 = 0xA9AC70C3L;
    for (l_3 = 1; (l_3 < 22); ++l_3)
    { 
        uint16_t l_7 = 0x4BC6L;
        return l_7;
    }
    for (l_4 = 8; (l_4 >= 5); l_4--)
    { 
        uint64_t l_10 = 18446744073709551613UL;
        l_10 = (-1L);
    }
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
