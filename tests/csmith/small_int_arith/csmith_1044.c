// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1044.c
#include "csmith.h"


static long __undefined;



static int64_t g_3 = 0x8901F2C29A3DF603LL;
static int8_t g_4 = 0x7BL;
static uint8_t g_6 = 0UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint8_t l_2 = 0x24L;
    int32_t l_5 = (-1L);
    g_3 &= l_2;
    if ((g_3 | 0xDDD3F467L))
    { 
        return g_3;
    }
    else
    { 
        int64_t l_11 = 1L;
        g_4 = (-2L);
        l_5 = (-3L);
        g_6 = 0x1DFE0091L;
        l_11 = (0x6BC3EC3D4E703026LL ^ (safe_rshift_func_uint8_t_u_s(0x73L, (safe_sub_func_int16_t_s_s(9L, g_3)))));
        return l_11;
    }
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
