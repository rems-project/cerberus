// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_836.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x8A61928CL;
static uint16_t g_9 = 65534UL;



static const uint64_t  func_1(void);




static const uint64_t  func_1(void)
{ 
    uint8_t l_5 = 0xA9L;
    int32_t l_11 = 8L;
    int16_t l_13 = (-8L);
    for (g_2 = 0; (g_2 == (-27)); g_2 = safe_sub_func_uint32_t_u_u(g_2, 8))
    { 
        uint16_t l_8 = 0x822BL;
        --l_5;
        g_9 |= l_8;
    }
    if (l_5)
    { 
        g_2 = 0x2B3B7BEDL;
    }
    else
    { 
        int32_t l_10 = 1L;
        g_2 = g_2;
        l_10 = l_5;
        l_11 = l_10;
        g_2 = g_2;
    }
    l_11 = g_9;
    if (g_2)
    { 
        g_2 = (-9L);
    }
    else
    { 
        int8_t l_12 = 8L;
        g_2 = (-1L);
        l_12 = g_9;
        g_2 &= g_9;
        l_13 |= l_11;
    }
    return l_11;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
