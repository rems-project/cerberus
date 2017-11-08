// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_912.c
#include "csmith.h"


static long __undefined;



static uint8_t g_6 = 0xD0L;
static uint32_t g_8 = 0UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int8_t l_2 = 0x7FL;
    uint8_t l_3 = 2UL;
    int32_t l_7 = 0L;
    l_3 = l_2;
    for (l_2 = 0; (l_2 >= 12); l_2 = safe_add_func_int8_t_s_s(l_2, 4))
    { 
        const uint16_t l_9 = 0xC88EL;
        g_6 = (-10L);
        l_7 ^= 0L;
        g_8 = 0x3B3F3656L;
        if (l_9)
            break;
    }
    l_7 = g_6;
    return g_6;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
