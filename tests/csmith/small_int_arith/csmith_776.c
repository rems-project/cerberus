// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_776.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 1UL;
static int32_t g_3 = (-1L);
static uint64_t g_5 = 0x44696A485BF25CBDLL;
static uint64_t g_7 = 18446744073709551606UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint16_t l_4 = 0xBACDL;
    g_3 |= g_2;
    g_5 &= l_4;
    if (g_5)
    { 
        int16_t l_6 = 0L;
        l_6 = l_4;
        g_7 = 4L;
    }
    else
    { 
        int32_t l_8 = 1L;
        l_8 ^= 0x1015AA96L;
    }
    return l_4;
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
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
