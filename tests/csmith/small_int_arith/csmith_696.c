// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_696.c
#include "csmith.h"


static long __undefined;



static int64_t g_6 = (-2L);
static uint64_t g_10 = 0x1B055CC25BFC88EBLL;
static int64_t g_12 = 7L;
static int32_t g_17 = 0x90350D8AL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int8_t l_2 = 1L;
    int32_t l_3 = 1L;
    uint64_t l_4 = 0UL;
    uint64_t l_5 = 0UL;
    int64_t l_14 = 0xC54C975158018D9DLL;
    int64_t l_15 = 1L;
    l_3 = l_2;
    if (l_4)
    { 
        g_6 |= l_5;
    }
    else
    { 
        uint16_t l_7 = 0x8F3CL;
        l_7++;
        return g_6;
    }
    if (l_4)
    { 
        int8_t l_11 = 0xDEL;
        g_10 ^= g_6;
        g_12 = l_11;
    }
    else
    { 
        int64_t l_13 = 8L;
        int32_t l_16 = 0x23E52509L;
        l_13 &= g_10;
        l_14 ^= (-1L);
        l_16 ^= l_15;
        g_17 = 1L;
    }
    return g_12;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
