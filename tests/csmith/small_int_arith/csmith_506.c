// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_506.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x2C03342EL;
static uint32_t g_6 = 0xEAC45307L;
static uint8_t g_8 = 3UL;
static uint32_t g_11 = 18446744073709551615UL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int16_t l_5 = 7L;
    int32_t l_7 = 0xDD1D8F8FL;
    for (g_2 = (-17); (g_2 != 22); g_2 = safe_add_func_uint64_t_u_u(g_2, 1))
    { 
        g_6 = l_5;
        l_7 = 7L;
    }
    if (g_2)
    { 
        ++g_8;
        g_2 = l_7;
        --g_11;
        g_2 = g_8;
    }
    else
    { 
        uint64_t l_14 = 18446744073709551612UL;
        l_14 = 0L;
        g_2 = g_11;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
