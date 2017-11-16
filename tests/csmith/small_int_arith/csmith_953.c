// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_953.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x60477862L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint64_t l_5 = 5UL;
    for (g_2 = 27; (g_2 != (-6)); g_2 = safe_sub_func_int64_t_s_s(g_2, 3))
    { 
        return l_5;
    }
    for (g_2 = (-16); (g_2 <= 4); g_2 = safe_add_func_uint32_t_u_u(g_2, 1))
    { 
        if (l_5)
            break;
    }
    return l_5;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
