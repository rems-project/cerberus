// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_739.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 0x0BB743D8L;
static uint32_t g_9 = 0UL;
static int16_t g_12 = (-8L);
static int64_t g_13 = (-2L);
static int16_t g_14 = 0xD2F3L;
static int8_t g_17 = 9L;
static uint16_t g_20 = 0x9228L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    const uint8_t l_2 = 0x9BL;
    int32_t l_4 = 0x871D976FL;
    int32_t l_5 = 0xFE1CA296L;
    int32_t l_6 = 0L;
    int32_t l_7 = 1L;
    int32_t l_8 = 0x279C4185L;
    int32_t l_15 = 0x7B6FE6D3L;
    int32_t l_16 = (-7L);
    int32_t l_18 = (-1L);
    int32_t l_19 = 9L;
    g_3 = l_2;
    ++g_9;
    g_3 = (-1L);
    g_20--;
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
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
