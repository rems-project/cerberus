// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_902.c
#include "csmith.h"


static long __undefined;



static int32_t g_6 = (-1L);
static uint16_t g_7 = 1UL;
static uint8_t g_11 = 0xCAL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint64_t l_2 = 0UL;
    int32_t l_5 = 0x759609C3L;
lbl_10:
    l_2 = 0x93B4E1A3L;
    for (l_2 = (-27); (l_2 == 58); l_2 = safe_add_func_uint64_t_u_u(l_2, 1))
    { 
        --g_7;
        if (l_2)
            goto lbl_10;
        g_11 = l_5;
    }
    l_5 = l_5;
    return l_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
