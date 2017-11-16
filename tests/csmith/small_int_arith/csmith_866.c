// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_866.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 18446744073709551609UL;
static uint32_t g_5 = 1UL;
static int32_t g_8 = 0x81A7ECC2L;
static uint32_t g_10 = 1UL;
static uint8_t g_14 = 0x4EL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint64_t l_2 = 0x3532FE2236432A27LL;
    int32_t l_9 = 1L;
    uint32_t l_15 = 0xF3AC9D73L;
    g_3 = l_2;
    if (l_2)
    { 
        int32_t l_4 = 0x72A8358BL;
        l_4 = l_2;
        ++g_5;
    }
    else
    { 
        g_8 |= g_3;
        if (g_3)
            goto lbl_13;
    }
    if (l_2)
    { 
        g_8 = 0x2D0DA0BDL;
    }
    else
    { 
lbl_13:
        g_10--;
        g_14 &= g_8;
        l_9 &= 0xACE4B0ADL;
        g_8 &= g_10;
    }
    return l_15;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
