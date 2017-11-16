// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_841.c
#include "csmith.h"


static long __undefined;



static const uint64_t g_2 = 0x115252CB13638ECFLL;
static uint32_t g_6 = 0UL;
static uint16_t g_8 = 0x2DAFL;
static uint64_t g_9 = 0xCD409884CB8F6C21LL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int16_t l_3 = 1L;
    l_3 = g_2;
    for (l_3 = (-4); (l_3 >= 25); l_3 = safe_add_func_int16_t_s_s(l_3, 7))
    { 
        int64_t l_7 = 0xF8F576C5165352F7LL;
        g_6 &= 0x3126FF23L;
        if (l_7)
            break;
        g_8 = g_2;
        g_9 = (-1L);
    }
    return g_8;
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
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
