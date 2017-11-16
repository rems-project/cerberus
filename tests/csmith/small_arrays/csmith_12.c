// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_12.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 5L;
static uint16_t g_14 = 0UL;



static const int32_t  func_1(void);




static const int32_t  func_1(void)
{ 
    uint8_t l_2 = 6UL;
    int32_t l_13 = 1L;
    int32_t l_15 = 0x9F42C60EL;
    g_3 &= (l_2 >= 0xC4D8E5CCC90A35F3LL);
    g_3 = g_3;
    l_15 ^= (((~0L) > g_3) <= (g_14 |= (safe_add_func_uint32_t_u_u((safe_lshift_func_int8_t_s_u((((safe_mod_func_int32_t_s_s((safe_div_func_int32_t_s_s((-1L), l_13)), l_13)) , g_3) != g_3), 0)), l_2))));
    return g_3;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
