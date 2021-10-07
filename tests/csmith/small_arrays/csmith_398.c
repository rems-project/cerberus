// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_398.c
#include "csmith.h"


static long __undefined;



static int16_t g_4 = 0x245FL;
static uint32_t g_5 = 0xCCE1E2C0L;
static uint32_t g_6 = 1UL;
static uint64_t g_7 = 18446744073709551615UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int32_t l_8[1];
    int i;
    for (i = 0; i < 1; i++)
        l_8[i] = 0L;
    g_6 = (g_5 = (safe_div_func_uint32_t_u_u(0x1FEBAEEFL, g_4)));
    g_7 &= g_4;
    return l_8[0];
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
