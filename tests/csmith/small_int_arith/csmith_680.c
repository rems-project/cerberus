// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_680.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static int16_t g_6 = 2L;
static int8_t g_7 = 1L;
static int16_t g_8 = (-5L);
static uint16_t g_12 = 65531UL;
static int8_t g_15 = 1L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    const int16_t l_5 = 6L;
    int64_t l_9 = 0L;
    int32_t l_10 = 0x021C3A23L;
    for (g_2 = 0; (g_2 >= 9); g_2 = safe_add_func_int16_t_s_s(g_2, 3))
    { 
        int32_t l_11 = 0x7ECC2443L;
        g_6 = l_5;
        g_7 = 0x17BE1879L;
        --g_12;
        g_15 = 1L;
    }
    return g_12;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
