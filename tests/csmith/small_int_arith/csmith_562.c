// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_562.c
#include "csmith.h"


static long __undefined;



static int16_t g_5 = 0x909BL;
static int16_t g_6 = 0x81CEL;
static int16_t g_7 = 0xBA1AL;
static int32_t g_9 = 0x9D221E9CL;
static uint64_t g_10 = 18446744073709551615UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    const int32_t l_2 = (-7L);
    int32_t l_13 = 0L;
    int32_t l_16 = (-1L);
    if (l_2)
    { 
        int64_t l_3 = 0xCCCE1E2C0D37AD43LL;
        int32_t l_4 = 1L;
        int32_t l_8 = 0L;
        l_3 = l_2;
        --g_10;
        l_13 = 0x4E912083L;
    }
    else
    { 
        g_9 = (-1L);
        g_9 = g_5;
    }
    l_13 = g_6;
    for (g_7 = 3; (g_7 != (-3)); g_7 = safe_sub_func_int32_t_s_s(g_7, 3))
    { 
        l_16 |= l_13;
        g_9 = 0xE2294BB4L;
    }
    return l_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
