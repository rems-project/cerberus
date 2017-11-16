// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_407.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 1UL;
static int64_t g_5 = 0xCAF14C90D29729CFLL;
static uint32_t g_7 = 0xE790E864L;
static int32_t g_9 = 0xB051AF7FL;
static uint32_t g_10 = 1UL;
static int32_t g_22 = 0x8ED7C3B7L;
static int32_t g_28 = 0x82ECC90CL;
static int16_t g_29 = 0x1692L;
static uint32_t g_31 = 0xACB2D505L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint8_t l_4 = 0x48L;
    int32_t l_26 = (-5L);
    int64_t l_30 = 0x9D073D4C46983C17LL;
    if (g_2)
    { 
        int64_t l_3 = (-8L);
        l_3 = g_2;
        l_4 = 0x7DD68876L;
        g_5 = l_3;
    }
    else
    { 
        int8_t l_6 = 9L;
        int32_t l_8 = 0x63D18804L;
        l_6 |= 0L;
        g_7 |= l_4;
        l_8 &= 4L;
        ++g_10;
    }
    for (l_4 = 0; (l_4 < 46); l_4 = safe_add_func_int8_t_s_s(l_4, 1))
    { 
        uint64_t l_15 = 0x6E74E80031AA08ECLL;
        int32_t l_18 = 0L;
        --l_15;
        l_18 = 5L;
    }
    for (g_2 = 11; (g_2 == 10); g_2--)
    { 
        int32_t l_21 = 0xC9F196E6L;
        l_21 = 0xE283D1F0L;
        g_22 = 0L;
        g_22 = g_7;
    }
    for (l_4 = 0; (l_4 < 52); l_4 = safe_add_func_int8_t_s_s(l_4, 1))
    { 
        int64_t l_25 = 0xAF14186E1459F451LL;
        int32_t l_27 = 0x42B4CF22L;
        ++g_31;
        if (l_25)
            continue;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    transparent_crc(g_29, "g_29", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
