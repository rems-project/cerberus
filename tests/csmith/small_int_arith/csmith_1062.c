// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1062.c
#include "csmith.h"


static long __undefined;



static int64_t g_4 = 0x9DADA439BEB0647DLL;
static int32_t g_14 = 0xB11F3813L;
static uint16_t g_40 = 0x4501L;
static uint16_t g_43 = 65535UL;
static int16_t g_49 = 1L;
static uint8_t g_58 = 8UL;
static int64_t g_67 = 9L;
static int32_t g_71 = (-3L);
static int16_t g_72 = (-1L);



static int64_t  func_1(void);
static uint16_t  func_7(int32_t  p_8, int32_t  p_9, uint8_t  p_10);




static int64_t  func_1(void)
{ 
    uint16_t l_6 = 0x24CDL;
    int32_t l_56 = 0x188558B0L;
    int32_t l_57 = 0L;
    l_6 |= (safe_rshift_func_int8_t_s_u(g_4, (!0L)));
    g_14 = (((func_7(l_6, (((((0x4B58E17C10977A12LL || (g_4 >= l_6)) || 0x7EE39F3FAA32F3F6LL) >= 0xE0L) && l_6) & 0x0BB94D0FL), g_4) >= 0x9A13L) , 0xDDAE974CA7790412LL) > 0L);
    if ((safe_rshift_func_int8_t_s_s(((safe_mul_func_int8_t_s_s((safe_rshift_func_uint16_t_u_s((safe_mul_func_int16_t_s_s((safe_sub_func_int8_t_s_s((safe_div_func_uint32_t_u_u((safe_sub_func_int8_t_s_s(g_4, g_14)), (safe_mul_func_uint8_t_u_u((safe_add_func_uint64_t_u_u(18446744073709551615UL, 0xAD058BBE58ED0BD2LL)), (-1L))))), l_6)), (-4L))), l_6)), 255UL)) & g_14), 4)))
    { 
        const int32_t l_35 = 0x89276496L;
        g_40 = (safe_div_func_int64_t_s_s((l_35 > func_7(((safe_div_func_int16_t_s_s((safe_add_func_int16_t_s_s((g_4 != 4L), g_4)), g_4)) == l_6), l_6, g_14)), g_4));
        if (g_4)
            goto lbl_68;
        g_43 = (g_14 , ((l_35 , (safe_rshift_func_uint8_t_u_u((0x4B54C5F6B4AB19F8LL != l_6), g_40))) < 1UL));
        g_49 &= (((safe_lshift_func_uint8_t_u_u(g_40, ((l_6 , (safe_unary_minus_func_uint64_t_u(func_7((safe_div_func_int32_t_s_s(0xC684CA67L, 2UL)), l_35, g_40)))) >= g_14))) > g_14) & 0x0EAAL);
lbl_68:
        g_67 = (safe_add_func_int32_t_s_s(((safe_add_func_int64_t_s_s(l_35, (safe_mod_func_uint16_t_u_u(((((g_58--) == (safe_mod_func_int64_t_s_s(l_35, (safe_sub_func_uint64_t_u_u((safe_add_func_int8_t_s_s(((g_43 < g_43) || 1UL), (-8L))), l_6))))) , 0xBDF5444FL) | l_57), 0x1BD9L)))) != 1UL), l_35));
        return g_49;
    }
    else
    { 
        uint32_t l_73 = 0x54D8FDC3L;
        int32_t l_76 = 0x33308626L;
        g_72 &= (g_71 = ((safe_sub_func_int8_t_s_s(0xFDL, l_57)) < 0x6A4358B9E0795B17LL));
        l_76 = (l_73 > ((((safe_sub_func_uint16_t_u_u(func_7(g_58, (g_43 , 0xA1EA5693L), l_73), g_4)) >= g_58) , g_67) , 1L));
        return l_57;
    }
}



static uint16_t  func_7(int32_t  p_8, int32_t  p_9, uint8_t  p_10)
{ 
    uint32_t l_11 = 0x71A05132L;
    l_11--;
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
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_40, "g_40", print_hash_value);
    transparent_crc(g_43, "g_43", print_hash_value);
    transparent_crc(g_49, "g_49", print_hash_value);
    transparent_crc(g_58, "g_58", print_hash_value);
    transparent_crc(g_67, "g_67", print_hash_value);
    transparent_crc(g_71, "g_71", print_hash_value);
    transparent_crc(g_72, "g_72", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
