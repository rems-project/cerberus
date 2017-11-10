// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1113.c
#include "csmith.h"


static long __undefined;



static int16_t g_5 = 5L;
static int16_t g_6 = 1L;
static int8_t g_7 = 0L;
static int32_t g_9 = (-1L);
static int32_t g_10 = 0x867B8F5FL;
static int32_t g_12 = (-10L);
static uint8_t g_17 = 0xAEL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int32_t l_2 = 0xE48D327CL;
    int32_t l_3 = 7L;
    int32_t l_4 = 0x61F66568L;
    int32_t l_8 = (-1L);
    int32_t l_11 = 1L;
    int32_t l_13 = 1L;
    int32_t l_14 = 0xC12265E3L;
    int32_t l_15 = (-4L);
    int32_t l_16 = (-2L);
    g_17--;
    return l_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
