// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_947.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static int64_t g_40 = (-8L);



static uint32_t  func_1(void);
static int32_t  func_21(uint32_t  p_22, uint16_t  p_23, uint32_t  p_24, uint64_t  p_25, uint16_t  p_26);




static uint32_t  func_1(void)
{ 
    uint16_t l_3 = 0x9532L;
    int32_t l_4 = 0xAD86E52DL;
    uint32_t l_34 = 1UL;
    int32_t l_36 = 0L;
    if ((g_2 = g_2))
    { 
        uint16_t l_5 = 0x8654L;
        int32_t l_10 = (-1L);
        l_3 = (g_2 = 0xF94F3783L);
        l_5--;
        l_10 &= (safe_add_func_uint16_t_u_u(((l_5 | g_2) , l_5), g_2));
        g_2 = (safe_rshift_func_uint16_t_u_u(((safe_add_func_uint8_t_u_u((safe_div_func_uint16_t_u_u((l_10 |= 0UL), 0xB979L)), l_3)) | g_2), 14));
    }
    else
    { 
        uint64_t l_19 = 0x40552487223B16AALL;
        int32_t l_20 = 1L;
        g_2 = (g_2 < l_4);
        l_20 &= ((safe_add_func_uint8_t_u_u((l_19 = 0x85L), g_2)) > 1UL);
        if (l_3)
            goto lbl_37;
    }
lbl_37:
    l_36 = (l_4 = func_21((safe_lshift_func_int8_t_s_s((safe_sub_func_int8_t_s_s(((!(((l_3 != 7UL) < l_4) | 0UL)) >= g_2), 6L)), 6)), l_3, l_3, g_2, l_34));
    g_40 |= (safe_add_func_int32_t_s_s((((l_36 , g_2) || g_2) >= l_36), l_34));
    l_4 = l_36;
    return l_36;
}



static int32_t  func_21(uint32_t  p_22, uint16_t  p_23, uint32_t  p_24, uint64_t  p_25, uint16_t  p_26)
{ 
    uint32_t l_35 = 1UL;
    g_2 = p_24;
    return l_35;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_40, "g_40", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
