// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_469.c
#include "csmith.h"


static long __undefined;



static int16_t g_4 = 0xB11AL;
static int16_t g_6 = (-8L);
static int32_t g_8 = (-8L);
static uint32_t g_9 = 4294967295UL;
static int8_t g_12 = 1L;
static uint32_t g_18 = 0UL;
static uint16_t g_19 = 0xE4C2L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int32_t l_2 = 0L;
    uint64_t l_13 = 18446744073709551615UL;
    if (l_2)
    { 
        uint8_t l_3 = 255UL;
        int32_t l_5 = 1L;
        int32_t l_7 = 0x5425A80EL;
        g_4 |= l_3;
        g_9--;
        l_13++;
        l_5 = l_7;
    }
    else
    { 
        int32_t l_16 = (-1L);
        int16_t l_17 = 0x9F58L;
        l_16 &= g_12;
        l_17 = g_12;
        g_18 &= g_8;
    }
    g_19 = (-1L);
    return l_13;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
