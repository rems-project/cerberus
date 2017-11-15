// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_475.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 7L;
static uint64_t g_5 = 18446744073709551611UL;
static uint32_t g_10 = 0x80CA9F8DL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint64_t l_6 = 0x8C3AD3B3152C58FBLL;
    uint64_t l_9 = 1UL;
    uint32_t l_14 = 0x95D1C58BL;
    uint16_t l_15 = 0x5B8BL;
    int32_t l_16 = 0x4B7C7008L;
    int32_t l_19 = 1L;
    for (g_2 = 0; (g_2 > (-22)); --g_2)
    { 
        g_5 = g_2;
        l_6++;
        if (g_2)
            goto lbl_13;
        l_9 &= 6L;
    }
    if (l_9)
    { 
lbl_13:
        g_10--;
        l_14 = g_2;
        l_16 &= l_15;
    }
    else
    { 
        int32_t l_17 = 0L;
        int32_t l_18 = 1L;
        l_18 ^= l_17;
        g_2 = g_10;
        l_17 ^= 0L;
        return l_19;
    }
    l_16 = l_9;
    return l_15;
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
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
