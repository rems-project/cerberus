// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1005.c
#include "csmith.h"


static long __undefined;



static uint16_t g_11 = 1UL;
static int8_t g_31 = 0xF2L;



static int64_t  func_1(void);
static uint8_t  func_3(uint32_t  p_4, int8_t  p_5, uint8_t  p_6);




static int64_t  func_1(void)
{ 
    uint16_t l_2 = 0x3644L;
    uint32_t l_30 = 1UL;
    int32_t l_32 = 0x4BE495EEL;
    g_31 = ((((l_2 || l_2) && ((func_3((((((((safe_add_func_uint64_t_u_u((((safe_rshift_func_int16_t_s_s(l_2, 15)) , g_11) <= g_11), g_11)) <= g_11) || 1L) , g_11) == 0x2A3CC92EA21E1D82LL) & l_2) , g_11), g_11, l_2) == g_11) , l_30)) , g_11) >= g_11);
    if (((l_32 &= l_2) != 0xD5L))
    { 
        return l_30;
    }
    else
    { 
        return g_31;
    }
}



static uint8_t  func_3(uint32_t  p_4, int8_t  p_5, uint8_t  p_6)
{ 
    int32_t l_16 = (-3L);
    int32_t l_23 = 0xE401D933L;
    int32_t l_24 = 0xB607800FL;
    int32_t l_25 = (-5L);
    int16_t l_29 = 1L;
    l_25 = (l_23 = ((l_24 |= (safe_mod_func_int16_t_s_s(((l_16 = (safe_rshift_func_int8_t_s_u(p_6, 6))) > ((safe_mod_func_int64_t_s_s((safe_rshift_func_uint16_t_u_s((safe_div_func_uint32_t_u_u((0L >= l_23), p_5)), 8)), g_11)) & g_11)), g_11))) <= g_11));
    l_24 ^= (safe_lshift_func_int8_t_s_u(((safe_unary_minus_func_uint8_t_u((((p_5 != 0x77L) > ((l_25 , g_11) >= g_11)) == l_29))) == p_4), l_23));
    return g_11;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
