// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_769.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = (-1L);
static uint64_t g_8 = 0xBE39E3CF95751CFDLL;
static int64_t g_9 = (-6L);



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint16_t l_3 = 0x976FL;
    int32_t l_7 = 5L;
lbl_6:
    g_2 |= 0x624039B6L;
    if (g_2)
    { 
        l_3--;
        if (l_3)
            goto lbl_6;
        l_7 = g_2;
        return l_7;
    }
    else
    { 
        g_8 = 0x4185A1FAL;
        g_9 = l_7;
        return g_9;
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
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
