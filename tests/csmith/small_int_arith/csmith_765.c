// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_765.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x342EB90DL;
static uint32_t g_3 = 0xCF54C3C6L;
static int8_t g_9 = (-9L);
static int8_t g_10 = 0x40L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int64_t l_7 = 5L;
    int32_t l_8 = 0x84BC9C3DL;
    int32_t l_11 = (-1L);
    int32_t l_12 = 0L;
    uint8_t l_13 = 0xB1L;
    if (g_2)
    { 
        uint16_t l_4 = 0xC453L;
        g_3 &= g_2;
        l_4 &= 1L;
        g_2 ^= 0x23B1A956L;
    }
    else
    { 
        int32_t l_5 = 0x6C516535L;
        int32_t l_6 = 0x7516A205L;
        l_13--;
    }
    l_11 = g_10;
    return g_9;
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
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
