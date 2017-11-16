// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_636.c
#include "csmith.h"


static long __undefined;



static int64_t g_5 = (-4L);
static int8_t g_6 = 0xC8L;
static int64_t g_12 = 0x844A754320E32CF4LL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int8_t l_2 = 1L;
    int32_t l_7 = 0L;
    int32_t l_8 = 8L;
    uint64_t l_9 = 7UL;
    if (l_2)
    { 
        uint32_t l_3 = 1UL;
        uint8_t l_4 = 246UL;
        l_4 = l_3;
        return g_5;
    }
    else
    { 
        g_6 &= g_5;
    }
    --l_9;
    g_12 = l_2;
    l_8 ^= (-1L);
    return g_12;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
