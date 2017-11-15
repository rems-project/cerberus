// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_914.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2 = 0UL;
static int8_t g_9 = (-2L);
static int32_t g_10 = 1L;
static int8_t g_13 = (-1L);
static uint32_t g_14 = 0x12D2C87AL;
static uint32_t g_18 = 0xCF592758L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    const uint64_t l_5 = 1UL;
    int32_t l_17 = 0x3E13A6C9L;
    g_2--;
    if (l_5)
    { 
        uint32_t l_6 = 1UL;
        int32_t l_7 = 1L;
        int32_t l_8 = 0x22A149CEL;
        int32_t l_11 = 6L;
        int32_t l_12 = 0xDB2BC40EL;
        l_6 = g_2;
        l_7 ^= l_6;
        ++g_14;
        l_17 = l_11;
    }
    else
    { 
        g_18 = l_17;
    }
    for (g_9 = (-28); (g_9 == 3); g_9 = safe_add_func_uint16_t_u_u(g_9, 1))
    { 
        return g_18;
    }
    return g_14;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
