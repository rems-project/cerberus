// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_522.c
#include "csmith.h"


static long __undefined;



static uint8_t g_4 = 0xE1L;
static uint16_t g_8 = 0x9C41L;
static int16_t g_13 = 8L;
static uint64_t g_14 = 18446744073709551608UL;
static int32_t g_18 = 0x2280643BL;
static uint32_t g_21 = 0xDFFBE584L;
static uint8_t g_24 = 0x59L;
static int8_t g_25 = 0x4CL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_2 = (-6L);
    uint64_t l_3 = 0x37BC75286E871D97LL;
    uint64_t l_7 = 8UL;
    if (l_2)
    { 
        l_3 = l_2;
    }
    else
    { 
        g_4++;
        l_7 = l_2;
        g_8 &= g_4;
    }
    l_2 = 1L;
    if (g_4)
    { 
        uint8_t l_9 = 0xE7L;
        int32_t l_12 = 0L;
        ++l_9;
        l_2 &= l_7;
        l_12 = g_4;
        g_14++;
    }
    else
    { 
        int8_t l_17 = 0xDEL;
        int32_t l_19 = (-2L);
        int32_t l_20 = (-1L);
        l_17 = 0xF7E44142L;
        g_21++;
        return g_8;
    }
    g_24 = 0L;
    return g_25;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
