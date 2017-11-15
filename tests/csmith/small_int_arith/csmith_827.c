// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_827.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 0x22BA3946L;
static uint16_t g_8 = 1UL;
static int64_t g_10 = (-10L);
static int64_t g_13 = 0x2EDA8ED40A165018LL;
static int16_t g_14 = 0x4F6CL;
static uint32_t g_16 = 0xBDA18461L;
static uint32_t g_18 = 0xF59EC134L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int64_t l_2 = (-3L);
    int32_t l_7 = 1L;
    uint32_t l_15 = 1UL;
    uint64_t l_19 = 0x84225189D9E62B56LL;
lbl_12:
    ++g_3;
    if (l_2)
    { 
        int32_t l_6 = 0xBB4EBB0CL;
        l_6 &= g_3;
        l_7 = l_6;
        g_8 = g_3;
    }
    else
    { 
        uint16_t l_9 = 0x1ADBL;
        int32_t l_11 = (-1L);
        l_7 = l_9;
        g_10 = l_7;
        l_11 |= g_8;
        if (l_2)
            goto lbl_12;
    }
    if (g_3)
    { 
        g_13 = 3L;
        if (l_2)
            goto lbl_17;
    }
    else
    { 
        g_14 = 0x8405CEFDL;
lbl_17:
        g_16 |= l_15;
        g_18 ^= g_13;
        l_7 ^= g_13;
    }
    return l_19;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
