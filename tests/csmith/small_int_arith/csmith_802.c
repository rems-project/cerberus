// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_802.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xAC204E2DL;
static int8_t g_5 = 0x39L;
static int16_t g_6 = 0x90BEL;
static int16_t g_7 = (-4L);
static int32_t g_8 = 9L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_12 = 0xAD8530DEL;
    int32_t l_13 = 7L;
    for (g_2 = (-1); (g_2 > 10); ++g_2)
    { 
        uint8_t l_9 = 0xEEL;
        g_5 &= g_2;
        l_9++;
        l_12 = l_9;
        l_13 = g_8;
    }
    for (g_7 = 2; (g_7 < 29); g_7 = safe_add_func_int64_t_s_s(g_7, 3))
    { 
        g_2 = 0xDC8DFBA2L;
    }
    return g_6;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
