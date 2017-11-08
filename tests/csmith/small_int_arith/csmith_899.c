// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_899.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x387FB0B0L;
static int8_t g_3 = 0L;
static int32_t g_4 = 0x3F365653L;
static int64_t g_7 = 4L;
static int16_t g_8 = 1L;
static uint32_t g_9 = 18446744073709551612UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int32_t l_5 = 0L;
    int32_t l_6 = (-6L);
    g_2 |= (-1L);
    if (g_2)
    { 
        g_3 = g_2;
    }
    else
    { 
        g_4 = 0x978F3C34L;
    }
    ++g_9;
    for (g_7 = 0; (g_7 <= 18); g_7++)
    { 
        l_6 &= (-8L);
    }
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
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
