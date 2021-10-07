// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_230.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 0x87013DCEL;
static int16_t g_6 = 0x72A7L;
static uint8_t g_8 = 6UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int32_t l_2 = 0x825E7A66L;
    int32_t l_4 = 1L;
    int32_t l_5[4] = {0x3B9DA4D0L,0x3B9DA4D0L,0x3B9DA4D0L,0x3B9DA4D0L};
    int32_t l_7 = 0x8D020BD2L;
    uint32_t l_13 = 0x59141A9CL;
    int i;
    g_3 = l_2;
    g_8--;
    for (g_3 = (-4); (g_3 <= 32); g_3 = safe_add_func_uint16_t_u_u(g_3, 3))
    { 
        return l_13;
    }
    return l_5[3];
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
