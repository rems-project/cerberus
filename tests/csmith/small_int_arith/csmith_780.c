// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_780.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static uint32_t g_5 = 0xB0E446DFL;
static int32_t g_12 = (-1L);
static uint32_t g_13 = 0x8CF4C59CL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int8_t l_8 = 1L;
    int32_t l_9 = 1L;
    int32_t l_10 = 8L;
    int32_t l_11 = (-7L);
    for (g_2 = 14; (g_2 == (-28)); g_2 = safe_sub_func_uint8_t_u_u(g_2, 1))
    { 
        g_5 = g_2;
        return g_5;
    }
    for (g_5 = 0; (g_5 <= 28); g_5 = safe_add_func_uint8_t_u_u(g_5, 1))
    { 
        l_8 = g_2;
        g_13--;
        g_12 = g_2;
        if (g_2)
            break;
    }
    return l_9;
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
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
