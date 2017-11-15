// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_734.c
#include "csmith.h"


static long __undefined;



static int64_t g_2 = 0L;
static uint8_t g_3 = 0x2EL;
static uint32_t g_8 = 0xAFA2FAFDL;
static uint32_t g_10 = 18446744073709551613UL;
static int32_t g_13 = (-10L);
static uint32_t g_15 = 1UL;
static uint64_t g_18 = 18446744073709551606UL;
static uint16_t g_19 = 65535UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint32_t l_7 = 6UL;
    int32_t l_12 = 0x9F8D19C9L;
    int32_t l_14 = (-1L);
    ++g_3;
    if (g_2)
    { 
        int16_t l_6 = 8L;
        int32_t l_9 = 0L;
        l_6 = g_3;
        g_8 = l_7;
        l_9 = l_7;
        g_10 |= g_8;
    }
    else
    { 
        int8_t l_11 = (-1L);
        uint16_t l_20 = 0x42E4L;
        ++g_15;
        g_18 = g_3;
        g_19 |= 0x7008B15EL;
        l_20 = g_3;
    }
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
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
