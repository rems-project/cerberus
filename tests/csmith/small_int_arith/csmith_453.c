// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_453.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-3L);
static int32_t g_6 = (-1L);



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    const uint16_t l_5 = 0x937DL;
    for (g_2 = 0; (g_2 != (-23)); g_2--)
    { 
        int32_t l_7 = 1L;
        g_6 = l_5;
        l_7 |= 0x1C76D7BEL;
        if (l_5)
            continue;
        g_6 |= 0x61BAB593L;
    }
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
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
