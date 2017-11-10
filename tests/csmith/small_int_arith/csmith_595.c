// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_595.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 5L;
static uint32_t g_9 = 0x5A945CB8L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint32_t l_2 = 18446744073709551615UL;
    int32_t l_5 = 0x04F3D4E6L;
    g_3 = l_2;
    g_3 = 0x13DCE9D0L;
    if (g_3)
    { 
        uint32_t l_4 = 0UL;
        g_3 = l_2;
        l_4 = (-1L);
        l_5 ^= l_4;
        g_3 = l_4;
    }
    else
    { 
        int32_t l_6 = 0x257EA0D0L;
        int32_t l_7 = (-1L);
        int32_t l_8 = 0x39D6B9C2L;
        g_3 = 8L;
        g_3 = 0x0CBEB969L;
        g_9--;
    }
    return g_3;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
