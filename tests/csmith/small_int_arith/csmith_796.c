// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_796.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 2UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int16_t l_3 = 0xDB50L;
    int32_t l_4 = (-1L);
    uint8_t l_8 = 0x73L;
    int32_t l_9 = 1L;
    l_3 &= g_2;
    if (l_3)
    { 
        uint8_t l_5 = 250UL;
        l_5--;
    }
    else
    { 
        l_8 = (-1L);
    }
    l_9 ^= l_4;
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
