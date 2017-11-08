// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_807.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x60477862L;
static int32_t g_5 = 0x8070ADE2L;
static uint32_t g_7 = 0xD9A924C0L;
static uint64_t g_27 = 18446744073709551615UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int64_t l_6 = 0xE08974B666A756A3LL;
    int32_t l_12 = 1L;
    int32_t l_13 = 0xC3A065C2L;
    int32_t l_15 = 0xBFB66FEBL;
    int32_t l_16 = (-1L);
    int32_t l_17 = 0xDF9C7750L;
    int32_t l_22 = (-1L);
    int32_t l_23 = 1L;
    for (g_2 = (-1); (g_2 >= 26); g_2 = safe_add_func_uint64_t_u_u(g_2, 5))
    { 
        int64_t l_10 = 3L;
        --g_7;
        return l_10;
    }
    if (l_6)
    { 
        g_2 = g_7;
        g_2 = l_6;
    }
    else
    { 
        int32_t l_11 = 0L;
        int32_t l_14 = 0L;
        int32_t l_18 = (-10L);
        int32_t l_19 = 0x4F5AC3D6L;
        int32_t l_20 = 0x36BE856DL;
        int32_t l_21 = 0x6A530863L;
        int32_t l_24 = (-10L);
        int32_t l_25 = 0x66AC3A60L;
        int32_t l_26 = (-7L);
        g_2 = l_11;
        g_27--;
        l_24 ^= g_2;
    }
    return g_7;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
