// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_608.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 4UL;
static uint16_t g_5 = 0x5260L;
static uint16_t g_9 = 0x8BD4L;
static int32_t g_15 = 0x885EA6EDL;
static uint64_t g_17 = 0x8EA5F34BDAC842F8LL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint8_t l_10 = 0x3AL;
    int32_t l_11 = 0xCD16652DL;
    g_2 = 0x9B55BB2CL;
    for (g_2 = 0; (g_2 < 48); ++g_2)
    { 
        int32_t l_8 = 0xA73D2D67L;
        g_5++;
        g_9 = l_8;
        l_10 = g_5;
        l_11 = g_5;
    }
    for (g_5 = (-18); (g_5 != 12); g_5 = safe_add_func_int16_t_s_s(g_5, 5))
    { 
        int16_t l_14 = 0x2B53L;
        int32_t l_16 = 2L;
        g_15 |= l_14;
        --g_17;
        g_15 = l_16;
    }
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
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
