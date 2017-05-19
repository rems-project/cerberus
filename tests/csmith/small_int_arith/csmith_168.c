// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_168.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x324EC2E0L;
static int16_t g_11 = 0xBEA5L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint8_t l_5 = 0x53L;
    int32_t l_6 = (-2L);
    const uint32_t l_10 = 0UL;
    int16_t l_12 = 1L;
    for (g_2 = 21; (g_2 <= (-9)); g_2 = safe_sub_func_uint64_t_u_u(g_2, 2))
    { 
        return g_2;
    }
    l_6 |= l_5;
    g_2 ^= ((((safe_rshift_func_int8_t_s_u(0x41L, 5)) < (g_11 = (+l_10))) | 0x3FL) < (-1L));
    g_2 = (l_12 & 1L);
    return g_11;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
