// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_842.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x7DDC85F7L;
static uint8_t g_9 = 0x1DL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int64_t l_13 = 0L;
    for (g_2 = 0; (g_2 <= 16); g_2++)
    { 
        int32_t l_5 = 6L;
        return l_5;
    }
    for (g_2 = 0; (g_2 == (-9)); g_2--)
    { 
        uint32_t l_8 = 0x77C8748AL;
        int32_t l_12 = 0xE86F8C7BL;
        l_8 = g_2;
        --g_9;
        l_12 = 2L;
        l_12 = g_9;
    }
    l_13 = 6L;
    return g_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
