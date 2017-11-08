// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_957.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 1UL;
static int32_t g_6 = 0xBE187950L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int8_t l_5 = 0x20L;
    int32_t l_10 = 1L;
    g_6 = (safe_lshift_func_uint8_t_u_s((g_4 ^ l_5), g_4));
    for (g_4 = (-15); (g_4 == 42); ++g_4)
    { 
        int32_t l_9 = 0x0BC5021CL;
        return l_9;
    }
    l_10 |= l_5;
    return l_5;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
