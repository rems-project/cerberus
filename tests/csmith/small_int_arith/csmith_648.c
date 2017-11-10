// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_648.c
#include "csmith.h"


static long __undefined;



static int32_t g_4 = 0xA9AC70C3L;
static int64_t g_5 = 1L;
static int32_t g_9 = 0xB3B7BEDEL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int8_t l_2 = 0x17L;
    int32_t l_3 = 0L;
    l_3 = l_2;
    g_5 = g_4;
    for (g_4 = 0; (g_4 != (-28)); g_4 = safe_sub_func_int64_t_s_s(g_4, 4))
    { 
        int16_t l_8 = (-6L);
        g_9 ^= l_8;
    }
    for (g_5 = (-30); (g_5 <= (-16)); g_5 = safe_add_func_uint8_t_u_u(g_5, 2))
    { 
        int64_t l_12 = 0xAFE8B0D193E0566ALL;
        g_9 = l_12;
    }
    return l_3;
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
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
