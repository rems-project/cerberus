// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_603.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 0xAF43L;
static uint32_t g_3 = 0x8C66F5A9L;
static int8_t g_6 = (-1L);
static uint8_t g_8 = 1UL;
static uint8_t g_9 = 255UL;
static int8_t g_10 = 0xAFL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    const uint32_t l_4 = 1UL;
    int32_t l_5 = 0xAA6E6F7FL;
    g_2 = 1L;
    if (g_2)
    { 
        g_3 = g_2;
        l_5 |= l_4;
    }
    else
    { 
        uint32_t l_7 = 6UL;
        g_6 |= 0xF90EF307L;
        l_7 = 0x754320E3L;
        g_8 = g_2;
        l_5 = g_6;
    }
    g_9 = l_5;
    g_10 = l_4;
    return l_5;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
