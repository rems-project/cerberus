// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_448.c
#include "csmith.h"


static long __undefined;



static uint8_t g_2 = 0UL;
static int32_t g_3 = 1L;
static uint8_t g_4 = 0x87L;
static int16_t g_6 = 0x7B5CL;
static int32_t g_7 = (-1L);
static int32_t g_8 = 1L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int32_t l_5 = 0xCA2961C0L;
    int32_t l_9 = 0L;
    uint32_t l_13 = 0x0EC01E6EL;
    uint64_t l_15 = 18446744073709551608UL;
    g_3 = g_2;
    g_4 = (-1L);
    if (g_4)
    { 
        uint8_t l_10 = 0x95L;
        l_10--;
        if (g_2)
            goto lbl_14;
lbl_14:
        l_13 = (-4L);
        return l_10;
    }
    else
    { 
        g_7 &= g_4;
        g_7 ^= 0xFE6D39C7L;
    }
    --l_15;
    return g_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
