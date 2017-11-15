// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_940.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 4294967292UL;
static int8_t g_6 = 1L;
static int32_t g_7 = 0xB80BE39EL;
static int8_t g_8 = (-1L);
static int64_t g_9 = 0x96673E7ED6F1860ELL;
static uint16_t g_11 = 0xA8B0L;
static uint32_t g_35 = 18446744073709551606UL;
static uint16_t g_38 = 0x097DL;



static uint32_t  func_1(void);
static const int32_t  func_19(uint32_t  p_20, uint16_t  p_21, uint32_t  p_22, int64_t  p_23);




static uint32_t  func_1(void)
{ 
    const uint32_t l_2 = 4294967290UL;
    uint32_t l_15 = 0xB9193C1DL;
    uint32_t l_32 = 0UL;
    int32_t l_34 = 0x300A9E1AL;
    if ((g_3 ^= (l_2 < l_2)))
    { 
        int32_t l_10 = 0xBFBD3AEBL;
        g_6 |= ((safe_sub_func_int32_t_s_s(0x1C0F8067L, 0x07B5CA98L)) ^ l_2);
        --g_11;
        return l_2;
    }
    else
    { 
        uint32_t l_14 = 4294967295UL;
        int32_t l_18 = 0xBE584996L;
        l_15 ^= (l_2 < l_14);
        l_18 = (g_7 ^= ((safe_mul_func_uint8_t_u_u((l_14 , g_11), l_14)) , g_9));
    }
    l_34 = func_19(((safe_add_func_uint8_t_u_u(((safe_mul_func_uint16_t_u_u(((safe_sub_func_int64_t_s_s((safe_lshift_func_int16_t_s_s(g_9, 9)), g_9)) != g_6), 1L)) != g_6), 0UL)) > 0x9C72L), l_2, l_32, l_32);
    g_35 &= ((g_7 & 0xB782L) < l_32);
    g_7 ^= (((g_38 ^= (safe_sub_func_int32_t_s_s(0xF181E214L, g_8))) == 9L) | 0xE094BF7DL);
    return l_15;
}



static const int32_t  func_19(uint32_t  p_20, uint16_t  p_21, uint32_t  p_22, int64_t  p_23)
{ 
    int16_t l_33 = (-4L);
    g_7 = p_23;
    l_33 ^= g_9;
    return l_33;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
