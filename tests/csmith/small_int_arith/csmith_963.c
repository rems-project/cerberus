// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_963.c
#include "csmith.h"


static long __undefined;



static int16_t g_10 = 2L;
static int32_t g_14 = 8L;
static int16_t g_17 = 1L;
static uint8_t g_21 = 0xBEL;
static int32_t g_33 = 1L;
static int32_t g_35 = 3L;
static int32_t g_36 = 0x5D07A051L;
static int16_t g_38 = 1L;
static uint8_t g_41 = 0xDBL;



static int16_t  func_1(void);
static int32_t  func_2(int16_t  p_3, int32_t  p_4, int16_t  p_5, int32_t  p_6);




static int16_t  func_1(void)
{ 
    int64_t l_9 = 0x8795010F7A73D2D6LL;
    int32_t l_50 = 0x9E855C71L;
    uint8_t l_53 = 0x1FL;
    l_50 = func_2((safe_rshift_func_int8_t_s_s(0L, l_9)), l_9, g_10, l_9);
    for (g_35 = 19; (g_35 < 4); g_35 = safe_sub_func_int32_t_s_s(g_35, 6))
    { 
        g_14 = (g_10 , g_10);
    }
    --l_53;
    return g_36;
}



static int32_t  func_2(int16_t  p_3, int32_t  p_4, int16_t  p_5, int32_t  p_6)
{ 
    uint32_t l_13 = 0x6EDAD94EL;
    int32_t l_32 = 0x9F2DC870L;
    int32_t l_34 = 0x4BE18A16L;
    int32_t l_39 = (-1L);
    if (((+(p_4 = (-2L))) & g_10))
    { 
        return p_4;
    }
    else
    { 
        p_4 = 0xF7CD95DAL;
    }
    g_14 = (p_4 = ((safe_unary_minus_func_uint32_t_u(p_6)) , l_13));
    if ((((g_17 = (safe_mul_func_uint8_t_u_u(g_14, l_13))) || p_5) , l_13))
    { 
        uint64_t l_18 = 0UL;
        int32_t l_37 = 0x95C588CBL;
        int32_t l_40 = 0x41824674L;
        int64_t l_46 = 0xB1F0CFADBACD6BCELL;
        l_18++;
        g_14 = g_10;
        g_14 |= 0xD177CCE4L;
        g_21 &= g_14;
        p_6 = g_14;
        g_14 = (safe_add_func_uint16_t_u_u((safe_div_func_uint16_t_u_u(((safe_mod_func_int8_t_s_s((safe_mod_func_uint32_t_u_u(((safe_sub_func_int32_t_s_s(((((g_21 < p_3) , l_18) || g_17) < l_18), g_17)) , 0xD2AFDDF3L), (-1L))), l_18)) == g_21), 0x9584L)), g_17));
        --g_41;
        p_4 = (((safe_add_func_uint64_t_u_u(((l_46 = g_17) ^ (-5L)), p_4)) , p_4) , l_37);
    }
    else
    { 
        uint32_t l_49 = 0x0AF36EAFL;
        l_49 = (safe_add_func_uint16_t_u_u((1UL || p_4), 0x26A0L));
    }
    return g_33;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_33, "g_33", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    transparent_crc(g_36, "g_36", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    transparent_crc(g_41, "g_41", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
