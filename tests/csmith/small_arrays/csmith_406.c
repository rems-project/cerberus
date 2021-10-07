// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_406.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 1L;
static uint32_t g_14 = 8UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint16_t l_13[2];
    int16_t l_16 = 5L;
    int i;
    for (i = 0; i < 2; i++)
        l_13[i] = 0x85C9L;
    for (g_2 = 0; (g_2 < (-16)); g_2 = safe_sub_func_uint8_t_u_u(g_2, 6))
    { 
        g_14 |= (safe_add_func_int8_t_s_s(g_2, (safe_add_func_int32_t_s_s((g_2 && (safe_div_func_int8_t_s_s((safe_sub_func_uint64_t_u_u((g_2 & l_13[0]), g_2)), g_2))), 0UL))));
        return g_2;
    }
    l_16 = ((g_2 , (~g_2)) == g_14);
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
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
