// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_617.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0x1A3622BAL;
static uint8_t g_5 = 0xA1L;
static int32_t g_7 = (-1L);
static uint32_t g_13 = 18446744073709551615UL;



static const int32_t  func_1(void);




static const int32_t  func_1(void)
{ 
    int16_t l_3 = 0xE17FL;
    uint16_t l_9 = 4UL;
    if (g_2)
    { 
        uint64_t l_4 = 0xB0CB8CE3E63E3155LL;
        int32_t l_6 = 1L;
        int32_t l_8 = 0xD658EDFEL;
        l_3 |= 0x8A59C176L;
        g_5 = l_4;
        l_6 = l_3;
        --l_9;
    }
    else
    { 
        uint32_t l_12 = 4294967295UL;
        l_12 = l_9;
        g_7 = g_7;
        return l_12;
    }
    --g_13;
    return l_3;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
