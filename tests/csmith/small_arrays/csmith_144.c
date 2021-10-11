// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_144.c
#include "csmith.h"


static long __undefined;



static int64_t g_10 = 0x221E9C96C7979B38LL;
static int32_t g_11 = (-1L);



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int8_t l_4 = 1L;
    int32_t l_5 = (-4L);
    uint64_t l_8[1];
    int i;
    for (i = 0; i < 1; i++)
        l_8[i] = 1UL;
    l_5 = (safe_lshift_func_uint8_t_u_u(l_4, 2));
    l_5 = (g_11 = ((safe_mod_func_uint64_t_u_u(((((l_8[0] > (((+l_4) , g_10) < l_8[0])) > l_8[0]) , g_10) != 4294967292UL), l_8[0])) && g_10));
    return g_10;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
