// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_567.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 4294967292UL;
static uint64_t g_7 = 0x8748AFA2FAFD11D9LL;
static uint8_t g_8 = 0UL;
static uint64_t g_9 = 0xA9F8D19C9214A9BALL;
static uint8_t g_10 = 249UL;
static uint64_t g_15 = 0x314A5EA964A90C6DLL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_14 = 7UL;
    int32_t l_16 = 0L;
    if (g_2)
    { 
        int32_t l_3 = 0xB546158DL;
        uint32_t l_4 = 0xAD3B3152L;
        l_4++;
        g_7 |= g_2;
        g_8 |= (-1L);
    }
    else
    { 
        int8_t l_13 = 0xADL;
        g_9 = 7L;
        --g_10;
        l_14 ^= l_13;
        g_15 ^= 0xCC4B7C70L;
    }
    l_16 |= g_2;
    for (g_7 = (-4); (g_7 >= 32); g_7 = safe_add_func_int32_t_s_s(g_7, 8))
    { 
        int64_t l_19 = 0x0E11A796D402DA3CLL;
        l_19 = g_15;
    }
    return g_10;
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
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
