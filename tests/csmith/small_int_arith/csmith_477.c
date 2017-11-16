// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_477.c
#include "csmith.h"


static long __undefined;



static int16_t g_3 = 0x50BFL;
static uint16_t g_4 = 0UL;
static uint64_t g_7 = 18446744073709551615UL;
static uint32_t g_11 = 4294967293UL;
static int8_t g_12 = 0x7FL;
static uint16_t g_14 = 0x5561L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int32_t l_2 = 0x13ECA4F8L;
    int32_t l_13 = 2L;
    g_3 |= l_2;
    l_2 = l_2;
lbl_9:
    if (g_3)
    { 
        g_4--;
        l_2 = g_4;
        l_2 = l_2;
        if (l_2)
            goto lbl_9;
        g_7 = g_4;
    }
    else
    { 
        uint32_t l_8 = 4294967293UL;
        return l_8;
    }
    if (l_2)
    { 
        int32_t l_10 = 0x7B051AF7L;
        l_2 = g_7;
        g_11 = l_10;
        g_12 = 0L;
        l_13 = l_10;
    }
    else
    { 
        g_14 = g_7;
    }
    return g_11;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
