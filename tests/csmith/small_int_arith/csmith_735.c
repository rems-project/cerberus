// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_735.c
#include "csmith.h"


static long __undefined;



static uint64_t g_11 = 4UL;
static uint32_t g_19 = 0x7919ADB8L;



static int8_t  func_1(void);
static int8_t  func_6(uint32_t  p_7, int32_t  p_8, const int16_t  p_9, const int64_t  p_10);




static int8_t  func_1(void)
{ 
    uint16_t l_12 = 1UL;
    const int8_t l_15 = (-4L);
    int32_t l_20 = 0x691F6F49L;
    l_20 = (safe_add_func_uint16_t_u_u((((((safe_mod_func_int8_t_s_s(func_6(((g_11 && l_12) < (safe_add_func_int16_t_s_s(l_12, l_12))), g_11, l_15, g_11), (-1L))) , (-1L)) , l_15) && g_19) > (-10L)), g_11));
    return g_19;
}



static int8_t  func_6(uint32_t  p_7, int32_t  p_8, const int16_t  p_9, const int64_t  p_10)
{ 
    uint64_t l_18 = 18446744073709551608UL;
    g_19 = (((l_18 = (safe_lshift_func_int8_t_s_s(0xBAL, (p_7 | ((-9L) > g_11))))) ^ p_9) != 0x36729694L);
    return g_19;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
