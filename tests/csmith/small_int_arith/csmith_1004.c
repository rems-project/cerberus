// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1004.c
#include "csmith.h"


static long __undefined;



static uint8_t g_3 = 0x57L;
static int64_t g_16 = 0xBBB4F5AC3D6C1DFELL;
static uint32_t g_20 = 1UL;



static uint64_t  func_1(void);
static uint16_t  func_6(int32_t  p_7, uint32_t  p_8, int8_t  p_9, uint64_t  p_10);




static uint64_t  func_1(void)
{ 
    int32_t l_2 = (-1L);
    if ((l_2 , g_3))
    { 
        return l_2;
    }
    else
    { 
        int8_t l_15 = 3L;
        uint8_t l_17 = 0xDFL;
        l_15 = ((l_2 , (safe_rshift_func_uint16_t_u_u((((func_6(g_3, ((+(safe_unary_minus_func_int64_t_s(((safe_add_func_uint8_t_u_u(g_3, g_3)) <= g_3)))) , g_3), l_2, g_3) == g_3) ^ g_3) || g_3), 15))) <= g_3);
        l_17--;
        g_20 = g_16;
        return l_2;
    }
}



static uint16_t  func_6(int32_t  p_7, uint32_t  p_8, int8_t  p_9, uint64_t  p_10)
{ 
    p_7 ^= g_3;
    return g_3;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
