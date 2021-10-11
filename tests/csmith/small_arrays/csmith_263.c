// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_263.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static uint64_t g_3 = 0x860B4FFB871C7BF0LL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint64_t l_6[2];
    int32_t l_9 = 0x7D2703D9L;
    int i;
    for (i = 0; i < 2; i++)
        l_6[i] = 0xBA33992443250E6DLL;
    g_3++;
    l_6[0]--;
    if (l_6[1])
    { 
        l_9 = (g_2 ^= (g_3 && g_3));
        l_9 = g_3;
        return g_2;
    }
    else
    { 
        return g_2;
    }
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
