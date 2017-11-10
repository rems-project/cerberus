// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_943.c
#include "csmith.h"


static long __undefined;



static int16_t g_7 = (-2L);
static uint32_t g_11 = 0UL;
static uint64_t g_30 = 18446744073709551614UL;
static int32_t g_45 = 6L;
static uint8_t g_47 = 0x12L;
static uint64_t g_50 = 18446744073709551611UL;
static uint32_t g_54 = 4294967290UL;



static int8_t  func_1(void);
static int32_t  func_2(uint8_t  p_3, uint8_t  p_4, uint32_t  p_5);




static int8_t  func_1(void)
{ 
    int8_t l_6 = (-1L);
    int32_t l_8 = 0x5A23E86FL;
    g_50 = func_2(((((l_6 ^ g_7) == g_7) >= 18446744073709551615UL) , g_7), l_8, g_7);
    for (l_6 = 0; (l_6 > 16); ++l_6)
    { 
        uint8_t l_53 = 0UL;
        return l_53;
    }
    ++g_54;
    return g_54;
}



static int32_t  func_2(uint8_t  p_3, uint8_t  p_4, uint32_t  p_5)
{ 
    int8_t l_12 = 0x43L;
    int32_t l_27 = 0x10CBEDFAL;
    int32_t l_40 = (-1L);
    int32_t l_42 = 8L;
    for (p_5 = 8; (p_5 != 29); p_5 = safe_add_func_uint64_t_u_u(p_5, 1))
    { 
        l_12 = (g_11 = p_5);
    }
    for (g_11 = 3; (g_11 <= 58); ++g_11)
    { 
        int32_t l_24 = 1L;
        int32_t l_25 = 0xA8DF0442L;
        int32_t l_26 = 0xEE1D4595L;
        l_27 = (safe_div_func_uint64_t_u_u((((((safe_mod_func_int16_t_s_s(((l_26 &= (+(safe_mul_func_uint16_t_u_u((safe_sub_func_uint64_t_u_u((l_25 = ((((l_24 >= l_12) < p_5) & g_7) , l_24)), g_7)), p_5)))) && g_7), 0x8E60L)) | g_11) == 0xC0998433L) != p_3) <= 0x79B347D17017A68FLL), g_11));
        g_30 = (safe_mod_func_int8_t_s_s(l_12, 0x50L));
        l_25 = (safe_rshift_func_uint16_t_u_u((safe_div_func_int64_t_s_s((((safe_mod_func_uint16_t_u_u((p_5 ^ l_24), p_3)) , 255UL) & p_5), g_11)), 6));
        if (p_4)
            continue;
    }
    for (g_7 = 0; (g_7 <= (-12)); g_7 = safe_sub_func_int16_t_s_s(g_7, 9))
    { 
        uint8_t l_39 = 0xE7L;
        int32_t l_41 = 0L;
        int32_t l_43 = 0xFF82244FL;
        int32_t l_44 = 0x555D5DF5L;
        int32_t l_46 = 7L;
        if (g_30)
            break;
        l_39 = (l_12 && g_7);
        ++g_47;
    }
    return l_42;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    transparent_crc(g_45, "g_45", print_hash_value);
    transparent_crc(g_47, "g_47", print_hash_value);
    transparent_crc(g_50, "g_50", print_hash_value);
    transparent_crc(g_54, "g_54", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
