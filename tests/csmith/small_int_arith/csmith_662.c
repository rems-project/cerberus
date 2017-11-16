// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_662.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 4L;
static int16_t g_13 = (-1L);
static uint32_t g_14 = 0xE6D39C7CL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint16_t l_5 = 1UL;
    int32_t l_6 = 0x76FF55E0L;
    int64_t l_11 = 0L;
    for (g_2 = (-16); (g_2 < (-26)); --g_2)
    { 
        return g_2;
    }
    l_6 = l_5;
    l_6 |= g_2;
    if (l_5)
    { 
        uint8_t l_7 = 255UL;
        int32_t l_10 = (-7L);
        ++l_7;
        l_10 ^= 0xFA147B80L;
        g_2 ^= l_11;
    }
    else
    { 
        uint32_t l_12 = 3UL;
        int32_t l_17 = 0L;
        g_2 = l_12;
        g_14++;
        l_17 = l_12;
    }
    return l_5;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
