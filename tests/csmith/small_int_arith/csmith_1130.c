// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1130.c
#include "csmith.h"


static long __undefined;



static int64_t g_7 = 0xC2A2C7C8A6B950BALL;
static int8_t g_9 = 0x09L;
static uint8_t g_10 = 0x5FL;
static uint8_t g_13 = 0UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_2 = 18446744073709551615UL;
    int32_t l_5 = 1L;
    int32_t l_6 = (-1L);
    int32_t l_8 = 0L;
    ++l_2;
    g_10--;
    --g_13;
    return l_6;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
