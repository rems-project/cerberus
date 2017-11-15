// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_600.c
#include "csmith.h"


static long __undefined;



static uint8_t g_2 = 0x0BL;
static uint32_t g_5 = 4294967295UL;
static uint32_t g_6 = 0UL;
static int16_t g_9 = 1L;
static int16_t g_12 = (-1L);
static uint32_t g_13 = 0UL;
static int16_t g_16 = (-8L);



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint64_t l_3 = 18446744073709551615UL;
    int32_t l_4 = (-1L);
    int32_t l_17 = 0L;
    int32_t l_18 = 0L;
    uint64_t l_19 = 1UL;
    l_3 &= g_2;
    if (g_2)
    { 
        l_4 = g_2;
        g_5 &= g_2;
    }
    else
    { 
        uint32_t l_10 = 0xED6F1860L;
        --g_6;
lbl_11:
        g_9 = 0xFA147B80L;
        l_10 = l_3;
        if (g_5)
            goto lbl_11;
    }
    ++g_13;
    ++l_19;
    return g_16;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
