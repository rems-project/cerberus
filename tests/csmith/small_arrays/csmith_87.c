// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_87.c
#include "csmith.h"


static long __undefined;



static uint16_t g_6 = 65535UL;
static uint64_t g_8 = 0x0A421E0BEC0351A9LL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int8_t l_7[3];
    int i;
    for (i = 0; i < 3; i++)
        l_7[i] = 0x43L;
    g_8 = (safe_sub_func_int16_t_s_s(((((safe_rshift_func_uint8_t_u_s(((((g_6 > (0x1ABEL ^ l_7[2])) , 1L) | (-1L)) & g_6), 1)) >= 0x52BF33880E033C22LL) < g_6) ^ 0x44B0L), 3UL));
    return l_7[1];
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
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
