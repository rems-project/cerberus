// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_945.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 4294967295UL;
static int32_t g_13 = 0x15D7249AL;
static uint64_t g_36 = 0UL;



static const uint32_t  func_1(void);
static int32_t  func_2(int16_t  p_3);




static const uint32_t  func_1(void)
{ 
    uint16_t l_22 = 0x98AAL;
    int32_t l_23 = 1L;
    int32_t l_24 = (-7L);
    uint32_t l_32 = 0x8C98AAC1L;
    int32_t l_35 = 0x8EB0BADCL;
    g_13 = func_2(g_4);
    l_24 &= (l_23 = (safe_mod_func_int16_t_s_s((safe_lshift_func_uint8_t_u_u((safe_div_func_int64_t_s_s((safe_add_func_int16_t_s_s(((g_4 > l_22) ^ g_13), g_4)), g_13)), g_13)), l_22)));
    if ((safe_sub_func_int8_t_s_s((safe_mod_func_int8_t_s_s((((((l_23 |= (+(safe_rshift_func_uint8_t_u_u(0x93L, 2)))) < 0x8661L) ^ g_4) , l_24) >= (-9L)), g_13)), l_32)))
    { 
        uint8_t l_33 = 255UL;
        int32_t l_34 = 0x3D975123L;
        l_24 &= ((g_13 || g_13) == g_13);
        l_33 = (4294967295UL || 4294967295UL);
        l_34 ^= (l_33 , g_13);
    }
    else
    { 
        g_36++;
    }
    for (l_22 = 23; (l_22 >= 28); ++l_22)
    { 
        return l_22;
    }
    return g_13;
}



static int32_t  func_2(int16_t  p_3)
{ 
    int16_t l_11 = 0xE6F7L;
    int32_t l_12 = 0x4A754320L;
    l_12 = (safe_mul_func_uint16_t_u_u(((safe_lshift_func_uint8_t_u_u((safe_sub_func_int16_t_s_s((g_4 || l_11), 1L)), 1)) != g_4), l_11));
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
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_36, "g_36", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
