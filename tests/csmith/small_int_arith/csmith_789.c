// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_789.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-1L);
static int32_t g_5 = 0x49FEBB67L;
static int32_t g_10 = 1L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int16_t l_7 = 0x3C63L;
    int32_t l_11 = (-1L);
    for (g_2 = (-22); (g_2 >= 10); g_2++)
    { 
        uint32_t l_6 = 1UL;
        g_5 = 3L;
        if (l_6)
            continue;
        return l_7;
    }
    for (g_5 = 0; (g_5 > (-7)); g_5 = safe_sub_func_int16_t_s_s(g_5, 2))
    { 
        g_2 |= (-8L);
        g_10 &= g_2;
    }
    l_11 |= (-1L);
    return g_5;
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
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
