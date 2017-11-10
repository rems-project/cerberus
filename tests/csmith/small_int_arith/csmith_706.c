// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_706.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2 = 0x3F4F46DB5052061FLL;
static int64_t g_3 = 1L;
static int16_t g_7 = 0xB4E7L;
static int32_t g_8 = 0L;
static uint32_t g_11 = 0x5C1D1022L;
static int32_t g_22 = 0x9A8551B3L;
static uint16_t g_24 = 65531UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    const int32_t l_4 = 3L;
    int32_t l_6 = 0xB8F5F499L;
    int32_t l_19 = 5L;
    int32_t l_20 = 0xC23EDB39L;
    int32_t l_21 = (-1L);
    int32_t l_23 = 1L;
    g_3 = g_2;
    if (l_4)
    { 
        uint64_t l_5 = 0x7822E6E7F737A9A9LL;
        int32_t l_9 = 0L;
        int32_t l_10 = (-1L);
        l_6 = l_5;
        l_6 = g_3;
        l_6 = g_2;
        ++g_11;
    }
    else
    { 
        uint64_t l_14 = 0x5D36729694D2B5F7LL;
        int32_t l_18 = 0L;
        --l_14;
        if (g_11)
            goto lbl_17;
lbl_17:
        g_8 = g_11;
        l_18 &= g_2;
    }
    ++g_24;
    l_23 &= g_2;
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
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
