// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_464.c
#include "csmith.h"


static long __undefined;



static const int32_t g_2 = 1L;
static uint16_t g_4 = 9UL;
static uint16_t g_5 = 0x4019L;
static int32_t g_8 = 0x37A9A971L;
static uint32_t g_16 = 0UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int16_t l_3 = 5L;
    int32_t l_14 = 1L;
lbl_12:
    l_3 = g_2;
    g_4 = l_3;
    if (l_3)
    { 
        uint32_t l_9 = 1UL;
        --g_5;
        g_8 = 4L;
        l_9--;
    }
    else
    { 
        g_8 = 0x6BA47C9DL;
        if (g_5)
            goto lbl_12;
    }
    if (l_3)
    { 
        int32_t l_13 = 8L;
        int32_t l_15 = 0x729694D2L;
        g_8 = l_13;
        l_14 = 0xDE0980DBL;
        l_15 = l_13;
        g_16++;
    }
    else
    { 
        uint32_t l_19 = 1UL;
        g_8 = l_19;
        g_8 = 0x6F49C23EL;
    }
    return l_14;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
