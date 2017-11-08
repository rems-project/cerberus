// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_806.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 4UL;
static int16_t g_11 = 7L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint32_t l_2 = 0xF01C0890L;
    int32_t l_12 = 0x83D78398L;
    if (l_2)
    { 
        int64_t l_6 = 0xF467215912491E29LL;
        --g_3;
        l_6 ^= 1L;
    }
    else
    { 
        uint64_t l_7 = 18446744073709551614UL;
        int32_t l_10 = 6L;
        --l_7;
        l_10 |= l_7;
        g_11 ^= l_2;
    }
    return l_12;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
