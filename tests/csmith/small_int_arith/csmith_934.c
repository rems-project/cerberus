// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_934.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x8C176B0FL;
static uint8_t g_14 = 0UL;
static int32_t g_15 = 0xC6578637L;



static const uint8_t  func_1(void);
static const int32_t  func_6(uint32_t  p_7, uint8_t  p_8, int64_t  p_9, uint64_t  p_10);




static const uint8_t  func_1(void)
{ 
    uint64_t l_3 = 0x1F94964A53AA9AC7LL;
    int32_t l_4 = 0x04822B16L;
    int32_t l_21 = 5L;
    l_3 &= g_2;
    if (g_2)
        goto lbl_5;
lbl_5:
    l_4 ^= g_2;
    if (g_2)
    { 
        int32_t l_11 = 0L;
        l_11 = func_6((g_2 , 0xC3938DD4L), g_2, g_2, g_2);
    }
    else
    { 
        int64_t l_20 = (-1L);
        g_2 |= (safe_sub_func_int32_t_s_s(0L, 0xE229EDCAL));
        g_15 ^= ((((g_14 = 0UL) | g_2) || l_4) , g_14);
        l_21 &= (((safe_rshift_func_int16_t_s_u(((safe_add_func_uint16_t_u_u(l_20, (-2L))) , 0x3DECL), l_4)) == 0xE1L) ^ g_14);
    }
    g_15 = (safe_rshift_func_int16_t_s_u((safe_rshift_func_int16_t_s_s(g_2, 13)), l_4));
    return g_2;
}



static const int32_t  func_6(uint32_t  p_7, uint8_t  p_8, int64_t  p_9, uint64_t  p_10)
{ 
    return p_8;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
