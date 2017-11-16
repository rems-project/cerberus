// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_711.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-1L);
static int32_t g_3 = 0x20FE6E32L;
static uint32_t g_9 = 0UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint64_t l_5 = 0x3F9E923E64F14790LL;
    int8_t l_6 = 0xEFL;
    int32_t l_7 = 0L;
    int32_t l_8 = 0L;
    if (g_2)
    { 
        int16_t l_4 = (-1L);
        g_3 = (-1L);
        l_5 = l_4;
    }
    else
    { 
        return g_3;
    }
    --g_9;
    for (l_5 = 0; (l_5 >= 28); l_5 = safe_add_func_int32_t_s_s(l_5, 3))
    { 
        return l_5;
    }
    return l_8;
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
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
