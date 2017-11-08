// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_923.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x8D327CB3L;
static int16_t g_7 = 0xA86BL;
static uint32_t g_8 = 0UL;
static uint32_t g_12 = 18446744073709551606UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint64_t l_4 = 0UL;
    int32_t l_6 = 2L;
    uint32_t l_15 = 4294967295UL;
    uint32_t l_19 = 0xE3CA3691L;
    if (g_2)
    { 
        int16_t l_3 = 0x83C8L;
        int32_t l_5 = 0x71867B8FL;
        g_2 &= l_3;
        l_4 ^= g_2;
        l_5 &= 0x3707822EL;
        g_8--;
    }
    else
    { 
        g_2 &= 0xE3EDFA83L;
        g_2 = g_7;
        if (g_7)
            goto lbl_18;
    }
    if (l_6)
    { 
        int32_t l_11 = 3L;
        g_12--;
    }
    else
    { 
        --l_15;
lbl_18:
        g_2 = (-3L);
        g_2 = g_2;
        l_19 ^= g_12;
    }
    l_6 = 0x3EDB3952L;
    return g_8;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
