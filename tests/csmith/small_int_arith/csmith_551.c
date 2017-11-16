// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_551.c
#include "csmith.h"


static long __undefined;



static int32_t g_4 = 0L;
static int8_t g_5 = 0x8FL;
static uint32_t g_6 = 18446744073709551611UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_2 = (-1L);
    int32_t l_3 = 0L;
    l_3 = l_2;
    if (l_3)
    { 
        g_4 = (-5L);
        g_5 = 0xA6DEEC54L;
        g_6 &= g_5;
    }
    else
    { 
        uint32_t l_7 = 0x3F5047C4L;
        int32_t l_8 = 2L;
        l_7 &= g_4;
        l_8 = 0xCE4A6F44L;
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
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
