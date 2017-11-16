// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_649.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 1L;
static int16_t g_7 = (-3L);



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int64_t l_6 = 4L;
    for (g_2 = (-19); (g_2 < 10); g_2++)
    { 
        int32_t l_5 = (-2L);
        l_6 = l_5;
        if (g_2)
            break;
        g_7 &= l_6;
    }
    if (l_6)
    { 
        int32_t l_8 = 4L;
        l_8 &= g_7;
        return g_7;
    }
    else
    { 
        uint64_t l_9 = 6UL;
        l_9 &= 0x76EC7516L;
        g_2 ^= l_9;
        g_2 = g_2;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
