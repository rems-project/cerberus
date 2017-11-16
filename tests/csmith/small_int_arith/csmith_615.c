// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_615.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x1824A8C6L;
static int8_t g_6 = 0x1DL;
static uint16_t g_7 = 0x3066L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int64_t l_5 = 0x1891F782A1836CCBLL;
    for (g_2 = 0; (g_2 >= 27); g_2 = safe_add_func_int16_t_s_s(g_2, 8))
    { 
        l_5 = 0L;
        g_7--;
    }
    for (g_7 = (-27); (g_7 <= 43); ++g_7)
    { 
        g_2 ^= (-3L);
        return g_7;
    }
    return l_5;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
