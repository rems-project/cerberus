// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_737.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 1UL;
static int32_t g_6 = 6L;
static uint32_t g_15 = 0xF7B6FE6DL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint8_t l_2 = 0xB7L;
    int32_t l_5 = 0x307B5CA9L;
    if (l_2)
    { 
        uint32_t l_3 = 0x871D976FL;
        g_4 |= l_3;
    }
    else
    { 
        uint8_t l_7 = 0x14L;
        l_5 &= (-1L);
        l_7++;
        return g_4;
    }
    for (g_4 = 23; (g_4 <= 54); g_4 = safe_add_func_uint32_t_u_u(g_4, 5))
    { 
        return g_6;
    }
    for (l_2 = 0; (l_2 >= 51); l_2++)
    { 
        uint16_t l_14 = 0xD2F3L;
        g_15 = l_14;
        if (l_14)
            continue;
        if (g_15)
            break;
    }
    return g_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
