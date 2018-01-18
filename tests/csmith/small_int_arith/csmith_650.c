// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_650.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0xEBAEEF20L;
static int8_t g_5 = 5L;
static int16_t g_6 = 0x0299L;
static int32_t g_7 = 0x6C7979B3L;
static int16_t g_9 = 1L;
static uint8_t g_12 = 0xF0L;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int32_t l_3 = (-4L);
    int32_t l_4 = 1L;
    g_2 = 0x7571177EL;
    l_3 = g_2;
    if (g_2)
    { 
        l_4 |= l_3;
        g_5 = 9L;
    }
    else
    { 
        int64_t l_8 = 0xE4E91208373B2C57LL;
        int32_t l_10 = 0xA96950A4L;
        int32_t l_11 = (-2L);
        g_6 = l_3;
        g_12++;
        l_11 = (-1L);
    }
    return l_4;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
