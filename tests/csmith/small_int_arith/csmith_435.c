// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_435.c
#include "csmith.h"


static long __undefined;



static uint16_t g_4 = 65529UL;
static uint8_t g_8 = 255UL;
static uint16_t g_15 = 65531UL;
static int32_t g_16 = 0L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int32_t l_2 = (-1L);
    int32_t l_3 = 4L;
    int32_t l_11 = 1L;
    int8_t l_18 = (-10L);
    g_4--;
    if (g_4)
        goto lbl_17;
    if (l_2)
    { 
        int16_t l_7 = (-1L);
        uint64_t l_12 = 0x81D21F1EB32A831DLL;
        l_7 = 1L;
        g_8++;
        l_12++;
    }
    else
    { 
        g_15 = l_3;
lbl_17:
        g_16 = (-4L);
        return l_18;
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
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
