// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1121.c
#include "csmith.h"


static long __undefined;



static uint64_t g_13 = 0UL;
static int32_t g_15 = 4L;
static int32_t g_19 = 2L;
static uint16_t g_20 = 0UL;



static uint32_t  func_1(void);
static uint32_t  func_5(uint32_t  p_6, uint32_t  p_7, uint8_t  p_8);




static uint32_t  func_1(void)
{ 
    int64_t l_9 = (-7L);
    uint32_t l_12 = 0xBF38C088L;
    int32_t l_21 = 1L;
    l_21 ^= (safe_rshift_func_uint16_t_u_u((~((g_20 |= (g_19 = func_5(l_9, l_9, (safe_rshift_func_uint16_t_u_u(l_9, l_12))))) || 0xC7104272L)), 10));
    l_21 |= (g_20 != l_12);
    return l_12;
}



static uint32_t  func_5(uint32_t  p_6, uint32_t  p_7, uint8_t  p_8)
{ 
    int64_t l_14 = 0x68819570A50B5F0BLL;
    uint64_t l_16 = 1UL;
    l_14 = g_13;
    l_16++;
    return g_15;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
