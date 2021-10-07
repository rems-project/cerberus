// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_209.c
#include "csmith.h"


static long __undefined;



static int16_t g_5 = 0x2443L;
static uint32_t g_6 = 0x43C4AB27L;
static uint16_t g_17 = 2UL;
static uint32_t g_22 = 0x52A28486L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_2 = 9L;
    int32_t l_12 = (-9L);
    uint16_t l_14 = 0xA26FL;
    l_2 = 0xA6847DFAL;
    for (l_2 = (-11); (l_2 != (-11)); ++l_2)
    { 
        uint16_t l_9 = 0x086BL;
        uint32_t l_13[2];
        int i;
        for (i = 0; i < 2; i++)
            l_13[i] = 0x95031536L;
        --g_6;
        --l_9;
        l_13[0] = (l_12 = l_9);
        if (g_5)
            break;
        --l_14;
        g_17 ^= l_13[0];
        if (l_14)
            break;
        g_22 = ((((safe_sub_func_int32_t_s_s((safe_add_func_uint16_t_u_u(65535UL, l_14)), (((0xFCE6BB2FL != l_13[0]) , l_9) , (-3L)))) ^ 65531UL) ^ 0x9E22401DBDAE4F9DLL) && l_12);
    }
    return l_14;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
