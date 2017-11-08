// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_35.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x324EC2E0L;
static int64_t g_7 = 1L;
static int16_t g_9 = (-1L);
static uint32_t g_13 = 0xEA5223FAL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int8_t l_6 = 0xB1L;
    int32_t l_8 = (-8L);
    int32_t l_10 = 0xE3580D41L;
    int32_t l_11 = 0L;
    int32_t l_12 = 0xAF8B5131L;
    for (g_2 = (-23); (g_2 >= (-29)); g_2--)
    { 
        int16_t l_5 = 0x1E42L;
        return l_5;
    }
    --g_13;
    return g_13;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
