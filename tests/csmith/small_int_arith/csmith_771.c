// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_771.c
#include "csmith.h"


static long __undefined;



static int32_t g_5 = 2L;



static const uint32_t  func_1(void);




static const uint32_t  func_1(void)
{ 
    int32_t l_2 = 0x252CB136L;
    l_2 = (-3L);
    for (l_2 = 0; (l_2 < 0); l_2 = safe_add_func_int32_t_s_s(l_2, 3))
    { 
        const uint8_t l_6 = 0x3BL;
        int32_t l_7 = 0x5E08CCCDL;
        g_5 ^= 6L;
        l_7 |= l_6;
        l_7 = 0x6C516535L;
    }
    return g_5;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
