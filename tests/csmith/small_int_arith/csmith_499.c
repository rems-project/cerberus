// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_499.c
#include "csmith.h"


static long __undefined;



static uint8_t g_2 = 0x03L;
static int32_t g_3 = 0x70BB743DL;
static uint8_t g_6 = 255UL;
static int16_t g_7 = (-1L);
static uint32_t g_8 = 6UL;
static uint32_t g_9 = 4294967291UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_12 = 0x96673E7EL;
    g_3 = g_2;
    for (g_3 = 9; (g_3 <= (-22)); g_3--)
    { 
        g_6 = g_3;
        g_7 = g_3;
    }
    g_8 &= 0x9C4185A1L;
    g_9++;
    return l_12;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
