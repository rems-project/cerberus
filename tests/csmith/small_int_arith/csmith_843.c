// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_843.c
#include "csmith.h"


static long __undefined;



static int32_t g_7 = 0xB51DBA33L;
static uint32_t g_10 = 0xEDCAD208L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint8_t l_2 = 0xA6L;
    int32_t l_5 = (-1L);
    int32_t l_6 = (-1L);
    int32_t l_8 = (-1L);
    int32_t l_9 = 0x043C4AB2L;
    l_2++;
    g_10--;
    l_5 ^= g_7;
    for (l_8 = 0; (l_8 <= 9); l_8 = safe_add_func_uint16_t_u_u(l_8, 5))
    { 
        uint32_t l_15 = 0x35CA4204L;
        l_15++;
    }
    return g_7;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
