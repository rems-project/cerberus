// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_432.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 0UL;
static uint32_t g_7 = 4294967288UL;
static uint32_t g_8 = 0x6E58D020L;
static uint32_t g_11 = 0x677B568BL;
static uint32_t g_12 = 0x1A9C2132L;
static int32_t g_14 = 2L;
static int8_t g_15 = 0x62L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint16_t l_2 = 65535UL;
    g_3 |= l_2;
    if (l_2)
    { 
        uint8_t l_4 = 0x25L;
        int32_t l_5 = (-6L);
        uint8_t l_6 = 0xFCL;
        l_5 &= l_4;
        g_7 &= l_6;
    }
    else
    { 
        g_8++;
lbl_13:
        g_11 = (-1L);
        g_12 = 0xF6F08421L;
        if (g_7)
            goto lbl_13;
    }
    if (l_2)
    { 
        g_14 |= (-6L);
    }
    else
    { 
        g_15 = 1L;
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
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
