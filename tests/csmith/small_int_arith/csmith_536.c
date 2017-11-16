// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_536.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-10L);
static uint32_t g_5 = 4294967289UL;
static int64_t g_6 = 0x1DFE4B283066C93ELL;
static uint16_t g_8 = 0UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint8_t l_11 = 254UL;
lbl_13:
    for (g_2 = (-2); (g_2 < (-16)); g_2--)
    { 
        return g_2;
    }
    if (g_2)
    { 
        int32_t l_7 = 0xB61D2250L;
        g_2 = g_2;
        g_5 &= g_2;
        ++g_8;
    }
    else
    { 
        uint64_t l_12 = 1UL;
        g_2 = g_2;
        l_12 = l_11;
        g_2 ^= (-1L);
        if (g_5)
            goto lbl_13;
    }
    return g_8;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
