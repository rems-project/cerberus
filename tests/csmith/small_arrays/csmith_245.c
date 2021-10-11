// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_245.c
#include "csmith.h"


static long __undefined;



static int32_t g_11 = 0x046B6EB6L;
static uint8_t g_13[1] = {0x42L};



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_2 = 0x1B3C692BL;
    int32_t l_7 = 0L;
    ++l_2;
    for (l_2 = (-12); (l_2 != 32); l_2++)
    { 
        uint32_t l_8 = 1UL;
        int32_t l_12 = 0xAA29C146L;
        g_11 = ((l_8--) , l_2);
        g_13[0]++;
        return l_8;
    }
    return g_13[0];
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_11, "g_11", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_13[i], "g_13[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
