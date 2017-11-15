// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_559.c
#include "csmith.h"


static long __undefined;



static uint16_t g_3 = 1UL;
static uint32_t g_4 = 0x48F69F7FL;
static uint64_t g_5 = 0x952EAA29C1464F16LL;
static uint32_t g_8 = 0xDAD5A519L;
static uint8_t g_9 = 255UL;
static int32_t g_11 = 0xD635290CL;
static uint16_t g_13 = 65526UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_2 = 0x692BEAA3L;
    int32_t l_6 = 0x9253A34CL;
    uint8_t l_14 = 0xD1L;
    if (l_2)
    { 
        g_4 = g_3;
        return g_4;
    }
    else
    { 
        uint32_t l_7 = 0x0657689AL;
        g_5 = 0x843046B6L;
        l_6 &= g_3;
        g_8 |= l_7;
        l_6 = g_5;
    }
    if (g_8)
    { 
        int64_t l_10 = 0x356EC7E434392F20LL;
        g_9 |= 0x1A652065L;
        l_10 = l_6;
    }
    else
    { 
        int32_t l_12 = 0x1FBB9CF7L;
        g_11 = g_8;
        g_13 |= l_12;
    }
    l_14 |= l_2;
    return g_9;
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
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
