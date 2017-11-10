// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_507.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0xB90DA115L;
static uint8_t g_3 = 0UL;
static uint8_t g_4 = 1UL;
static uint32_t g_5 = 0x565E08CCL;
static int8_t g_8 = (-1L);



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint32_t l_11 = 0x09884CB8L;
    int32_t l_12 = 0x8E9934B0L;
    if (g_2)
    { 
        g_3 &= 0xCF54C3C6L;
        g_4 = (-10L);
        g_5++;
    }
    else
    { 
        uint8_t l_9 = 0xBDL;
        int32_t l_10 = 0x4BC9C3D0L;
        g_8 ^= g_3;
        l_10 &= l_9;
    }
    l_12 = l_11;
    return g_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
