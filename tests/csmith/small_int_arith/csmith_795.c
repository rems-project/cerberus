// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_795.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 0x5D16L;
static uint8_t g_4 = 0xA8L;
static int32_t g_7 = 0x2B000CD9L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int64_t l_3 = 0x288A137B1891F782LL;
    g_2 = (-1L);
    if (l_3)
    { 
        int32_t l_5 = 0x66C93EE3L;
        g_4 &= l_3;
        l_5 &= 1L;
        return g_4;
    }
    else
    { 
        uint32_t l_6 = 0xBE9FB1C0L;
        l_6 &= g_2;
        g_7 ^= (-1L);
    }
    return l_3;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
