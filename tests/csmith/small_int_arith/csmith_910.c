// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_910.c
#include "csmith.h"


static long __undefined;



static uint64_t g_4 = 0x8C3AD3B3152C58FBLL;
static int32_t g_7 = (-4L);
static int64_t g_8 = 0x2EE6D058A835A23ELL;
static uint64_t g_9 = 0xB5C6EFF3DE0369BDLL;
static int64_t g_12 = 0x214A9BACDE9E8436LL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint8_t l_2 = 0x76L;
    int32_t l_14 = 0x2858905BL;
    uint8_t l_15 = 0x4BL;
    if (l_2)
    { 
        uint16_t l_3 = 1UL;
        return l_3;
    }
    else
    { 
        ++g_4;
        g_7 ^= l_2;
        --g_9;
        if (g_7)
            goto lbl_13;
    }
lbl_13:
    g_12 ^= g_4;
    l_14 = g_4;
    return l_15;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
