// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1131.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 1L;
static uint32_t g_5 = 18446744073709551608UL;
static uint16_t g_14 = 0x2513L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    for (g_2 = (-12); (g_2 >= 24); g_2 = safe_add_func_uint8_t_u_u(g_2, 9))
    { 
        uint16_t l_8 = 0x9831L;
        int32_t l_11 = 7L;
        int8_t l_15 = 1L;
        --g_5;
        l_8++;
        l_11 = g_5;
        if (l_8)
            break;
        g_14 &= ((safe_mod_func_uint8_t_u_u(l_8, g_5)) < g_2);
        return l_15;
    }
    for (g_14 = 0; (g_14 >= 14); g_14++)
    { 
        uint64_t l_18 = 0x207182B4746A1C17LL;
        return l_18;
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
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
