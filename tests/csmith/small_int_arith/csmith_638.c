// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_638.c
#include "csmith.h"


static long __undefined;



static const uint64_t g_2 = 0xA394643CDF98A59CLL;
static int64_t g_4 = (-1L);
static uint16_t g_5 = 65535UL;
static uint32_t g_10 = 1UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int32_t l_3 = 0xFBB4EBB0L;
    int32_t l_9 = 0xDF1ADB2BL;
    int32_t l_11 = 0xA6C9CD49L;
    uint16_t l_12 = 1UL;
    const int8_t l_14 = 0x77L;
    if (g_2)
    { 
        l_3 = 5L;
        if (g_2)
            goto lbl_8;
        g_4 = 5L;
    }
    else
    { 
lbl_8:
        --g_5;
        l_9 ^= l_3;
        g_10 = l_9;
    }
    l_11 = 0x2D91509CL;
    if (l_3)
    { 
        l_11 = 0x2758E92EL;
    }
    else
    { 
        uint8_t l_13 = 255UL;
        int32_t l_15 = 0x84255EBDL;
        l_13 = l_12;
        l_15 &= l_14;
    }
    return l_11;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
