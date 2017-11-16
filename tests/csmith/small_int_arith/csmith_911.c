// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_911.c
#include "csmith.h"


static long __undefined;



static uint8_t g_2 = 0UL;
static int8_t g_5 = 0x0BL;
static uint32_t g_9 = 0x94D03572L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_3 = 0xB25B3B9DL;
    int32_t l_4 = 0L;
    if (g_2)
    { 
        l_3 = g_2;
    }
    else
    { 
        uint32_t l_6 = 8UL;
        l_4 |= 0xF82FF40FL;
        g_5 &= g_2;
        l_6 = g_2;
    }
    for (g_5 = (-8); (g_5 == 17); g_5++)
    { 
        l_4 = 7L;
    }
    g_9 = g_5;
    return l_3;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
