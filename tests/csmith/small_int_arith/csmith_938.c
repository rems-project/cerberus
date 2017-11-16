// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_938.c
#include "csmith.h"


static long __undefined;



static int8_t g_10 = 0xEBL;
static int32_t g_18 = 0x41311E2DL;



static int64_t  func_1(void);
static int16_t  func_6(uint32_t  p_7, int32_t  p_8);




static int64_t  func_1(void)
{ 
    uint64_t l_9 = 0x121AC4888999D94BLL;
    int32_t l_29 = 4L;
    int32_t l_30 = 0x520C3D8DL;
    l_30 &= ((safe_rshift_func_uint16_t_u_s((((l_29 ^= (safe_mul_func_int16_t_s_s(func_6((l_9 || 0x3281L), g_10), g_10))) >= l_9) | g_10), l_9)) , 0x21BA52B3L);
    for (g_10 = (-22); (g_10 > 11); g_10++)
    { 
        const int32_t l_53 = 0x005767A0L;
        int32_t l_54 = (-3L);
        int32_t l_55 = 0xE67B33DFL;
        l_29 ^= ((((safe_mod_func_uint32_t_u_u((safe_div_func_uint64_t_u_u(g_18, 1UL)), (-6L))) || 0UL) , g_18) && g_10);
        l_55 = (safe_div_func_int64_t_s_s((l_54 |= (safe_add_func_int64_t_s_s((safe_mod_func_int8_t_s_s(((safe_div_func_int64_t_s_s(((safe_mul_func_int8_t_s_s(((safe_mod_func_uint16_t_u_u((safe_mod_func_uint8_t_u_u((safe_add_func_int8_t_s_s(0x2EL, l_29)), g_10)), g_10)) && 0xD78BL), 0UL)) > l_53), l_53)) && 0x97C2L), l_30)), l_30))), 18446744073709551608UL));
        g_18 = (0x21L & g_10);
        l_55 ^= (safe_mul_func_int8_t_s_s(((safe_add_func_int32_t_s_s(((!(7UL | g_18)) , 1L), l_54)) != 0xB1L), g_18));
    }
    return l_30;
}



static int16_t  func_6(uint32_t  p_7, int32_t  p_8)
{ 
    int32_t l_15 = 0xBE56890CL;
    int32_t l_16 = 0xD4A55F07L;
    int32_t l_17 = (-1L);
    l_17 = (safe_rshift_func_int16_t_s_u((((safe_sub_func_uint8_t_u_u(((l_16 = (l_15 & p_8)) , g_10), l_15)) , g_10) != p_7), 7));
    if ((l_16 , l_15))
    { 
        g_18 = (4UL == p_7);
        l_16 ^= (((g_18 , 0x5537C57F39CEE24BLL) >= 0x809B4AF7BDD48407LL) > 0x4FL);
        p_8 = g_10;
lbl_28:
        g_18 &= (g_10 > 0xF2F3L);
    }
    else
    { 
        g_18 |= 0L;
    }
    for (l_15 = 8; (l_15 == (-8)); l_15 = safe_sub_func_uint8_t_u_u(l_15, 6))
    { 
        uint64_t l_26 = 0xA104ACD6BA8DAD4FLL;
        int32_t l_27 = (-1L);
        p_8 = (safe_rshift_func_int16_t_s_s((g_18 != g_10), 1));
        l_27 = (safe_rshift_func_uint8_t_u_u((((!(g_18 , p_8)) >= 0x7C8A36A77D77FC7DLL) , l_26), 4));
        if (p_7)
            goto lbl_28;
    }
    g_18 = l_17;
    return g_18;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
