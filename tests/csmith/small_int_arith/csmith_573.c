// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_573.c
#include "csmith.h"


static long __undefined;



static uint8_t g_2 = 251UL;
static int32_t g_4 = 0x94DDBC37L;
static uint64_t g_7 = 0xBA47C9D5FAC12265LL;
static int32_t g_19 = 0x66C1932EL;
static uint64_t g_20 = 0xF6F49C23EDB39523LL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int32_t l_3 = 0xC8FC558BL;
    int32_t l_12 = (-1L);
    int32_t l_13 = 0xD1022782L;
    int32_t l_14 = (-5L);
    int32_t l_15 = 0x9694D2B5L;
    int32_t l_16 = 0xDB821342L;
    int32_t l_17 = (-9L);
    int32_t l_18 = (-1L);
    int32_t l_23 = 1L;
    g_2 = (-2L);
    if (l_3)
    { 
        uint32_t l_5 = 1UL;
        int32_t l_6 = 0L;
        g_4 = l_3;
        l_5 |= l_3;
        l_6 ^= g_4;
        if (l_5)
            goto lbl_11;
    }
    else
    { 
        uint16_t l_10 = 9UL;
        --g_7;
        l_10 = g_4;
    }
lbl_11:
    l_3 = g_2;
    g_20--;
    return l_23;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
