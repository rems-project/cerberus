// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_670.c
#include "csmith.h"


static long __undefined;



static uint64_t g_3 = 0xDB5052061F665683LL;
static int16_t g_4 = 0x4C40L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    const int8_t l_2 = 0L;
    int32_t l_8 = (-1L);
    g_3 = l_2;
    g_4 = 0L;
    for (g_4 = 14; (g_4 >= (-13)); --g_4)
    { 
        uint16_t l_7 = 9UL;
        l_7 = 0x867B8F5FL;
    }
    l_8 = (-10L);
    return g_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
