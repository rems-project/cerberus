// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_679.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x48BBCA63L;
static uint8_t g_5 = 0x62L;
static uint8_t g_6 = 0x7AL;



static const int32_t  func_1(void);




static const int32_t  func_1(void)
{ 
    for (g_2 = 14; (g_2 > 27); g_2++)
    { 
        uint8_t l_7 = 0x44L;
        g_5 = 0xB4E1265AL;
        g_6 = g_2;
        --l_7;
        return l_7;
    }
    if (g_6)
    { 
        uint16_t l_10 = 0xA527L;
        g_2 ^= 2L;
        g_2 = l_10;
    }
    else
    { 
        int64_t l_11 = 0x7C10977A1245C810LL;
        l_11 &= (-1L);
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
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
