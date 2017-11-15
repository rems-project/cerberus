// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_512.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 5L;
static int64_t g_6 = (-10L);
static uint64_t g_10 = 0x7F451D52AA0A5DECLL;
static int64_t g_14 = 1L;
static uint16_t g_15 = 0xD7BCL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int64_t l_5 = 0L;
    int32_t l_7 = 0x94B2AB76L;
    int32_t l_8 = 0x644ACCB2L;
    int32_t l_9 = 0x59EEDA58L;
    if (g_2)
    { 
        uint64_t l_3 = 18446744073709551606UL;
        int32_t l_4 = 1L;
        l_4 ^= l_3;
        l_5 = g_2;
        return l_5;
    }
    else
    { 
        uint32_t l_13 = 0x700D62E6L;
        g_6 = 0xFA20BD03L;
        g_10--;
        g_14 = l_13;
        g_15 = g_2;
    }
    l_7 = g_2;
    l_9 |= g_6;
    return g_2;
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
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
