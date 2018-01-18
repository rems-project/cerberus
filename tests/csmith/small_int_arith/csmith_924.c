// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_924.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static uint64_t g_4 = 0xF4A8B108F8256A9ELL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int8_t l_3 = 0L;
    int8_t l_7 = 0x4BL;
    int32_t l_10 = (-1L);
    g_4--;
    if (g_2)
    { 
        uint8_t l_8 = 0xD2L;
        int32_t l_9 = (-1L);
        g_2 = (-1L);
        l_8 = l_7;
        l_9 = l_3;
        g_2 = l_3;
    }
    else
    { 
        uint32_t l_11 = 0UL;
        l_10 = (-7L);
        g_2 = g_2;
        l_10 |= (-2L);
        l_11 ^= 0x7C70AB22L;
    }
    return g_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
