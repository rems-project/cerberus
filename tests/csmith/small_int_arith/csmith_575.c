// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_575.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xDF99FF60L;
static int64_t g_6 = 2L;
static uint16_t g_7 = 65533UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint64_t l_8 = 0UL;
    for (g_2 = (-1); (g_2 <= (-19)); g_2--)
    { 
        int8_t l_5 = 0x44L;
        l_5 ^= g_2;
        g_6 ^= 0L;
        if (l_5)
            continue;
        if (l_5)
            goto lbl_9;
        g_7 = g_6;
    }
lbl_9:
    l_8 = g_2;
    for (g_7 = (-10); (g_7 > 44); g_7 = safe_add_func_int32_t_s_s(g_7, 4))
    { 
        int8_t l_12 = 0x01L;
        int32_t l_13 = 0xA4DF6F97L;
        g_2 ^= l_12;
        l_13 |= g_2;
        l_13 &= g_2;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
