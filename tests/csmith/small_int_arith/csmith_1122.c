// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1122.c
#include "csmith.h"


static long __undefined;



static int32_t g_6 = 0L;
static uint64_t g_8 = 0x8C443EB60693009CLL;
static uint64_t g_16 = 3UL;
static uint8_t g_17 = 1UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint8_t l_7 = 254UL;
    uint16_t l_15 = 0x47BBL;
    g_8 = (safe_add_func_int16_t_s_s((((g_6 || (l_7 > g_6)) < l_7) && g_6), 0UL));
    g_17 = (((safe_lshift_func_uint8_t_u_u((safe_lshift_func_uint8_t_u_u((safe_sub_func_int64_t_s_s((g_16 = l_15), 0xDC0E3E7631615E82LL)), g_8)), l_15)) || 0x67C28CAE2FE81720LL) != g_6);
    return g_6;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
