// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_516.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2 = 0xD7F825E7A66FE7D8LL;
static int16_t g_3 = 0L;
static int32_t g_4 = (-10L);
static int64_t g_6 = 0L;
static uint8_t g_10 = 0x16L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int16_t l_8 = 0xBE13L;
    int32_t l_9 = 0xF0842170L;
    if (g_2)
    { 
        uint64_t l_5 = 0UL;
        g_3 = g_2;
        g_4 = g_3;
        g_6 = l_5;
    }
    else
    { 
        int32_t l_7 = (-1L);
        return l_7;
    }
    l_9 = l_8;
    g_10 = 0L;
    return g_3;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
