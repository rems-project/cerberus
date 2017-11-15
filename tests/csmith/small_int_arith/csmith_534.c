// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_534.c
#include "csmith.h"


static long __undefined;



static int16_t g_8 = 0xD2D6L;
static uint32_t g_9 = 4294967291UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_2 = 0UL;
    int32_t l_5 = 2L;
    l_2--;
    l_5 = l_2;
    for (l_5 = 0; (l_5 <= 11); l_5 = safe_add_func_int8_t_s_s(l_5, 6))
    { 
        g_9 = g_8;
    }
    return l_5;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
