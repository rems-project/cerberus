// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_851.c
#include "csmith.h"


static long __undefined;



static uint64_t g_4 = 2UL;
static int32_t g_5 = 0x7FD1E814L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    const uint16_t l_2 = 0UL;
    int32_t l_3 = 0xCECB4571L;
    l_3 = l_2;
    g_5 = g_4;
    for (l_3 = 0; (l_3 > 21); l_3 = safe_add_func_uint32_t_u_u(l_3, 7))
    { 
        int8_t l_8 = 0xFAL;
        g_5 = g_5;
        l_8 = g_4;
        g_5 = (-7L);
        return l_8;
    }
    return l_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
