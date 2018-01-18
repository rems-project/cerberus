// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_472.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xD313DD33L;
static int16_t g_7 = 0x987FL;
static int16_t g_8 = 0L;
static int16_t g_10 = (-3L);
static int64_t g_11 = 0x4B2AB76D6092F644LL;
static uint16_t g_12 = 0xCE55L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint8_t l_6 = 0x9FL;
    int32_t l_9 = 1L;
    for (g_2 = (-2); (g_2 != 24); ++g_2)
    { 
        const int64_t l_5 = 1L;
        if (g_2)
            break;
        l_6 |= l_5;
        g_12--;
    }
    if (g_7)
    { 
        uint16_t l_15 = 0x2AA0L;
        g_2 |= l_15;
        return l_9;
    }
    else
    { 
        int16_t l_16 = (-1L);
        int32_t l_17 = 0L;
lbl_18:
        g_2 &= l_16;
        l_17 = g_8;
        l_9 = (-5L);
        if (l_9)
            goto lbl_18;
    }
    l_9 = g_10;
    return l_9;
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
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
