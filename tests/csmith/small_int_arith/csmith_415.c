// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_415.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = (-4L);
static uint32_t g_3 = 0x7BF0B96CL;
static int8_t g_4 = 1L;
static int64_t g_6 = 0x6BD085C9E53E58BFLL;
static uint64_t g_7 = 0x03D9B950315362DALL;
static uint64_t g_10 = 0x420452A26F3F17E2LL;
static int32_t g_13 = 0x37C1D6B3L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint64_t l_5 = 18446744073709551615UL;
    int32_t l_14 = (-5L);
    if (g_2)
    { 
        g_3 = g_2;
    }
    else
    { 
        g_4 = 4L;
        l_5 = 6L;
        --g_7;
    }
    --g_10;
    g_13 = l_5;
    l_14 &= (-9L);
    return g_2;
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
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
