// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_840.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = 1L;
static int64_t g_4 = 0L;
static int8_t g_6 = 0x89L;
static uint64_t g_9 = 0x4A754320E32CF415LL;
static uint64_t g_11 = 2UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint8_t l_5 = 0xC4L;
    int32_t l_10 = 0L;
    uint16_t l_14 = 0xBD65L;
    if (g_2)
    { 
        const int8_t l_3 = 0xE9L;
        int32_t l_8 = 0L;
        g_4 = l_3;
        if (l_3)
            goto lbl_7;
lbl_7:
        g_6 = l_5;
        l_8 = (-8L);
    }
    else
    { 
        g_9 &= 0x7D7C1188L;
        l_10 = g_6;
        g_11++;
    }
    if (l_14)
    { 
        int32_t l_15 = 0xB27FA3DFL;
        uint64_t l_16 = 0x912530A9BCA7B5CFLL;
        l_15 = g_4;
        l_10 = g_2;
        return l_16;
    }
    else
    { 
        return g_2;
    }
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
