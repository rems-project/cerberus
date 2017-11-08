// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_825.c
#include "csmith.h"


static long __undefined;



static uint8_t g_4 = 0x29L;
static int32_t g_5 = (-8L);
static uint8_t g_8 = 0x68L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_2 = 0xA32B1CECB457102DLL;
    if (l_2)
    { 
        uint64_t l_3 = 0x1E814B733C633843LL;
        l_3 ^= l_2;
        g_4 ^= l_3;
    }
    else
    { 
        g_5 |= 1L;
    }
    for (l_2 = 0; (l_2 <= 17); l_2 = safe_add_func_int16_t_s_s(l_2, 4))
    { 
        return l_2;
    }
    g_8 = g_4;
    return g_5;
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
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
