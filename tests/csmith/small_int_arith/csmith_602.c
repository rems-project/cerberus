// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_602.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 0xCB3FL;
static int32_t g_3 = (-1L);
static uint8_t g_5 = 0UL;
static uint8_t g_8 = 1UL;
static int32_t g_11 = 0x0069F30CL;



static const int8_t  func_1(void);




static const int8_t  func_1(void)
{ 
    int8_t l_4 = 0xC0L;
    int32_t l_7 = 1L;
    g_3 = g_2;
    if (g_2)
    { 
        return g_2;
    }
    else
    { 
        int32_t l_6 = 7L;
        g_5 = l_4;
        --g_8;
    }
    g_11 = l_4;
    l_7 = 0x6BA47C9DL;
    return g_8;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
