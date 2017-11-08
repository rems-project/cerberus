// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_587.c
#include "csmith.h"


static long __undefined;



static int8_t g_4 = 1L;
static uint16_t g_5 = 65535UL;
static int32_t g_7 = (-3L);
static uint8_t g_8 = 0xC8L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint8_t l_2 = 0x04L;
    int32_t l_11 = 0x1AFA9B64L;
    if (l_2)
    { 
        int8_t l_3 = 1L;
        g_4 = l_3;
        g_5 = g_4;
    }
    else
    { 
        uint64_t l_6 = 0x34EEA2A3B3F36565LL;
        g_7 = l_6;
        g_8--;
    }
    l_11 = 0x6038591BL;
    l_11 ^= g_5;
    l_11 = l_2;
    return g_7;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
