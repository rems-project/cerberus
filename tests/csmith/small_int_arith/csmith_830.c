// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_830.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0xD33A4A9BDBA76AABLL;
static int16_t g_5 = 0L;
static int8_t g_6 = 0xABL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_3 = 4294967295UL;
    int32_t l_7 = (-8L);
    if (g_2)
    { 
        return l_3;
    }
    else
    { 
        int16_t l_4 = 0x0F1DL;
        l_4 = 8L;
        g_5 = g_2;
    }
    g_6 = 0xE4B7834DL;
    l_7 = (-1L);
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
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
