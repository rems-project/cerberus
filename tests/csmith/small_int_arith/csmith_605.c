// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_605.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 4294967292UL;
static uint16_t g_5 = 1UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint64_t l_2 = 1UL;
    int32_t l_6 = 0x9BA095A9L;
    int32_t l_7 = (-1L);
    uint8_t l_8 = 255UL;
    if (l_2)
    { 
        uint8_t l_4 = 0xA7L;
        g_3 &= 0L;
        l_4 |= g_3;
    }
    else
    { 
        g_5 |= 0x67F5ED9AL;
        l_8++;
    }
    l_7 = 0L;
    return g_5;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
