// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_520.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = 0L;
static uint16_t g_3 = 0x9831L;
static int8_t g_4 = 1L;
static uint32_t g_5 = 0x8C443EB6L;
static int8_t g_7 = 0x4DL;
static uint32_t g_12 = 9UL;



static const uint32_t  func_1(void);




static const uint32_t  func_1(void)
{ 
    int8_t l_6 = (-1L);
    int32_t l_11 = (-1L);
    if (g_2)
    { 
        uint16_t l_8 = 0UL;
        g_3 &= 0xA473EB90L;
        g_4 = g_3;
        g_5 = g_2;
        l_8++;
    }
    else
    { 
        l_11 = g_4;
        ++g_12;
        if (g_4)
            goto lbl_15;
lbl_15:
        l_11 &= 0xB583DC0EL;
        return g_5;
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
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
