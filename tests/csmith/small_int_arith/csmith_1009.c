// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1009.c
#include "csmith.h"


static long __undefined;



static int16_t g_6 = 0xE566L;
static int8_t g_8 = 8L;
static int16_t g_14 = (-5L);
static int32_t g_16 = (-8L);
static uint64_t g_20 = 0xFFF12F3CCD2466E9LL;
static uint32_t g_23 = 0x9BA87A5EL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint8_t l_2 = 0x1FL;
    int32_t l_3 = (-9L);
    int32_t l_4 = 0xB0E446DFL;
    int32_t l_5 = 0xB34E6D4FL;
    int32_t l_7 = 0xBA07E4FCL;
    int32_t l_9 = 8L;
    int32_t l_10 = 0L;
    int32_t l_11 = 1L;
    int32_t l_12 = 1L;
    int32_t l_13 = 0L;
    int32_t l_15 = 5L;
    int32_t l_17 = (-1L);
    int32_t l_18 = 0x145CCB97L;
    int32_t l_19 = 0xB1B6FD43L;
    l_3 = l_2;
    --g_20;
    g_16 &= g_6;
    g_23++;
    return l_13;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
