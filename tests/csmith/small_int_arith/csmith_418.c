// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_418.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0L;
static int32_t g_5 = 0L;
static uint8_t g_6 = 0x14L;
static int8_t g_9 = (-8L);
static uint32_t g_10 = 0x25D2D915L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_8 = 0x90A23371L;
    int8_t l_11 = 2L;
    int32_t l_12 = 0x08FB0B44L;
    if (g_2)
    { 
        int32_t l_3 = 0x43CDF98AL;
        uint64_t l_4 = 0x3EFC07E17F759609LL;
        l_4 = l_3;
    }
    else
    { 
        g_5 = g_2;
    }
    if (g_2)
        goto lbl_7;
lbl_7:
    g_6 = g_5;
    if (l_8)
    { 
        g_9 = (-6L);
        g_10 = 0L;
        l_12 = l_11;
    }
    else
    { 
        l_12 = l_8;
    }
    return l_12;
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
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
