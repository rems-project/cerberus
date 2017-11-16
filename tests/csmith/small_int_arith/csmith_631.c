// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_631.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 9L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint16_t l_2 = 0xF46DL;
    uint8_t l_7 = 0x7FL;
    int32_t l_10 = (-1L);
    g_3 = l_2;
    if (l_2)
        goto lbl_4;
lbl_4:
    g_3 = 0x558BAC04L;
    for (g_3 = 0; (g_3 >= (-26)); g_3 = safe_sub_func_uint64_t_u_u(g_3, 8))
    { 
        ++l_7;
    }
    l_10 = (-2L);
    return l_7;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
