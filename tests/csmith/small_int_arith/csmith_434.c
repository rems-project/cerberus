// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_434.c
#include "csmith.h"


static long __undefined;



static uint64_t g_11 = 8UL;
static uint32_t g_12 = 0xA9A97186L;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint8_t l_2 = 1UL;
    int32_t l_5 = (-9L);
    l_2--;
    l_5 ^= l_2;
    for (l_2 = 2; (l_2 != 45); l_2 = safe_add_func_int8_t_s_s(l_2, 1))
    { 
        uint32_t l_8 = 2UL;
        --l_8;
        if (g_11)
            continue;
        g_12++;
    }
    l_5 ^= l_2;
    return l_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
