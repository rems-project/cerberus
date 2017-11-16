// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_456.c
#include "csmith.h"


static long __undefined;



static int16_t g_4 = (-1L);
static int64_t g_9 = 0xB80BE39E3CF95751LL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint8_t l_2 = 0UL;
    uint64_t l_10 = 0UL;
    if (l_2)
    { 
        uint8_t l_3 = 9UL;
        l_3 = 0x743D837BL;
    }
    else
    { 
        return g_4;
    }
    for (g_4 = 0; (g_4 != (-8)); g_4--)
    { 
        return g_4;
    }
    for (g_4 = 0; (g_4 >= (-14)); g_4 = safe_sub_func_int32_t_s_s(g_4, 5))
    { 
        g_9 ^= g_4;
    }
    l_10 = l_2;
    return l_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
