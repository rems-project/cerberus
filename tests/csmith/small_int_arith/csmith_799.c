// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_799.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0x176B0F73838A1F94LL;
static int32_t g_7 = 9L;
static int8_t g_8 = 0x05L;
static uint8_t g_9 = 255UL;
static int16_t g_12 = 6L;
static int16_t g_13 = (-1L);
static int64_t g_14 = 0xA8FECF7921E124DCLL;
static uint64_t g_15 = 1UL;
static int16_t g_18 = 0x6917L;
static uint32_t g_21 = 0UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int32_t l_3 = 0xAA9AC70CL;
    const uint32_t l_4 = 0xD811F07BL;
    uint32_t l_6 = 0x8DD44AD3L;
    uint32_t l_20 = 1UL;
    l_3 = g_2;
    l_3 = l_3;
    if (l_4)
    { 
        int16_t l_5 = 0L;
        l_6 = l_5;
    }
    else
    { 
        uint64_t l_19 = 0xDE1FC657863718BDLL;
        ++g_9;
        g_15--;
        g_18 = g_15;
        l_19 = g_18;
    }
    g_21 ^= l_20;
    return g_21;
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
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
