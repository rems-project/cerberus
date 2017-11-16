// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_511.c
#include "csmith.h"


static long __undefined;



static const uint32_t g_2 = 0x57976326L;
static int8_t g_3 = (-1L);
static int8_t g_4 = 0xEBL;
static int32_t g_8 = 1L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int16_t l_5 = 0xF181L;
    int32_t l_9 = 0xC92EA21EL;
    uint32_t l_12 = 4UL;
    int32_t l_13 = (-3L);
    if (g_2)
    { 
        g_3 = g_2;
        g_4 = 1L;
        l_5 |= g_2;
    }
    else
    { 
        uint16_t l_6 = 0x6507L;
        int32_t l_7 = 0L;
        l_7 &= l_6;
        g_8 = 4L;
        l_7 = l_7;
        g_8 = g_8;
    }
    l_9 = l_5;
    for (l_9 = 0; (l_9 > (-28)); l_9 = safe_sub_func_uint32_t_u_u(l_9, 4))
    { 
        l_13 = l_12;
    }
    return l_13;
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
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
