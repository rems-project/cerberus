// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_837.c
#include "csmith.h"


static long __undefined;



static uint8_t g_2 = 0x52L;
static int16_t g_7 = (-1L);



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_3 = (-1L);
    int32_t l_6 = (-7L);
    l_3 = g_2;
    for (g_2 = 22; (g_2 > 27); g_2 = safe_add_func_uint32_t_u_u(g_2, 9))
    { 
        l_6 = l_3;
        g_7 = g_2;
        l_6 ^= 0x68044455L;
    }
    return g_7;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
