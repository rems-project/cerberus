// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_762.c
#include "csmith.h"


static long __undefined;



static int32_t g_4 = 8L;
static int16_t g_6 = 1L;
static int32_t g_10 = 0x253A34C8L;
static uint32_t g_11 = 1UL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int16_t l_2 = 0x2BEAL;
    int32_t l_3 = (-8L);
    int32_t l_9 = 4L;
    l_3 = l_2;
    g_4 = g_4;
    if (g_4)
    { 
        uint32_t l_5 = 4294967295UL;
        return l_5;
    }
    else
    { 
        int64_t l_7 = 1L;
        int32_t l_8 = 0xFA42B483L;
        g_6 |= g_4;
        l_7 = g_4;
        g_11++;
    }
    return l_9;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
