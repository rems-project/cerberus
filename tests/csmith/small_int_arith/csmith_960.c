// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_960.c
#include "csmith.h"


static long __undefined;



static uint16_t g_4 = 0x7D45L;
static int16_t g_5 = 0x5664L;
static int32_t g_6 = 1L;
static int64_t g_7 = 6L;
static int32_t g_26 = 0x6D64BDA9L;
static int16_t g_49 = (-9L);
static uint32_t g_50 = 0x376A9523L;



static uint8_t  func_1(void);
static int32_t  func_8(int8_t  p_9, int64_t  p_10, const uint64_t  p_11);




static uint8_t  func_1(void)
{ 
    g_7 = ((safe_rshift_func_int16_t_s_s((g_5 = ((g_4 , g_4) || 65526UL)), g_6)) || 9UL);
    g_50 = (g_49 &= func_8(g_7, g_6, g_6));
    return g_50;
}



static int32_t  func_8(int8_t  p_9, int64_t  p_10, const uint64_t  p_11)
{ 
    uint64_t l_18 = 0x27289FFF12F3CCD2LL;
    int32_t l_19 = 0x00D5493EL;
    uint32_t l_25 = 2UL;
    int32_t l_28 = 0xEF8A6EBBL;
    int8_t l_36 = (-1L);
    int32_t l_48 = 0L;
    if ((l_19 = (safe_lshift_func_uint8_t_u_s((safe_add_func_uint32_t_u_u((safe_rshift_func_int8_t_s_s(((0xCBL == g_6) > l_18), 6)), l_18)), 6))))
    { 
        int16_t l_22 = (-10L);
        int32_t l_27 = (-7L);
        l_22 = (safe_div_func_uint64_t_u_u(0xEAFB5D1CB6A7F4EALL, l_18));
        l_27 = ((g_26 = (safe_div_func_int8_t_s_s(l_25, p_9))) && l_22);
        l_28 |= g_5;
    }
    else
    { 
        int16_t l_29 = 0L;
        uint32_t l_37 = 1UL;
        int32_t l_40 = (-6L);
        g_26 = (((l_29 >= 0x800FL) && 0UL) < g_7);
        g_26 = (safe_mul_func_uint8_t_u_u(((safe_sub_func_uint64_t_u_u((safe_lshift_func_uint8_t_u_s(((l_18 > l_19) , p_10), l_36)), l_29)) || 0UL), l_37));
        g_26 = (safe_lshift_func_uint16_t_u_u((g_7 > g_4), 7));
        l_40 ^= (-3L);
    }
    g_26 = (~(safe_mul_func_uint8_t_u_u(((65534UL | g_4) || l_19), 0xC1L)));
    l_19 = ((0x99C826FFL != p_9) , p_9);
    l_48 = (l_19 ^= ((safe_lshift_func_uint16_t_u_s(((safe_rshift_func_int16_t_s_s(6L, l_36)) , 4UL), 3)) | g_26));
    return p_11;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_49, "g_49", print_hash_value);
    transparent_crc(g_50, "g_50", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
