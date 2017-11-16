// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_518.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 0xB0B02971L;
static int32_t g_4 = 0x39ED080CL;
static uint8_t g_6 = 1UL;
static int32_t g_9 = 0xF5D870A3L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int64_t l_2 = (-1L);
    int32_t l_7 = (-7L);
    int32_t l_8 = 1L;
    g_3 = l_2;
    if (l_2)
    { 
        uint16_t l_5 = 0UL;
        g_4 = 1L;
        g_6 = l_5;
        l_7 = g_6;
    }
    else
    { 
        l_8 &= l_7;
        g_9 = g_6;
        return l_7;
    }
    l_7 &= l_2;
    g_9 &= 0xC54C9751L;
    return g_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
