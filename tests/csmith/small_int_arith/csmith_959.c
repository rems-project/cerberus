// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_959.c
#include "csmith.h"


static long __undefined;



static uint32_t g_7 = 18446744073709551614UL;
static const int32_t g_14 = (-2L);
static int16_t g_15 = 0x0426L;
static uint8_t g_17 = 3UL;



static int16_t  func_1(void);
static int64_t  func_2(int32_t  p_3, uint16_t  p_4, int8_t  p_5, uint8_t  p_6);




static int16_t  func_1(void)
{ 
    uint8_t l_16 = 0UL;
    g_17 |= (func_2(g_7, g_7, g_7, g_7) | l_16);
    return g_15;
}



static int64_t  func_2(int32_t  p_3, uint16_t  p_4, int8_t  p_5, uint8_t  p_6)
{ 
    int8_t l_10 = 0xE9L;
    int32_t l_11 = 0xB77278FAL;
    l_11 = (((safe_rshift_func_uint8_t_u_s(((g_7 , 0xCB63E8E1B88146CDLL) >= l_10), 7)) && p_4) , l_10);
    for (p_6 = 0; (p_6 != 33); p_6 = safe_add_func_int64_t_s_s(p_6, 4))
    { 
        g_15 = (((0x9E9D60A2215256EELL != g_14) , p_5) <= 0x7A32L);
        return p_5;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
