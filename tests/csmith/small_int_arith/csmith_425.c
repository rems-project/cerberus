// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_425.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 0x07E17F75L;
static int32_t g_9 = (-1L);



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int32_t l_2 = 0x43CDF98AL;
    int32_t l_8 = 0xC79E672CL;
    uint64_t l_14 = 1UL;
    if (l_2)
    { 
        int16_t l_6 = 1L;
        int32_t l_7 = 0x551DA622L;
        uint32_t l_10 = 0xADF1ADB2L;
        g_3--;
        ++l_10;
    }
    else
    { 
        int64_t l_13 = 0x012D2C87A7525D2DLL;
        l_13 = g_3;
    }
    l_8 = l_14;
    return l_8;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
