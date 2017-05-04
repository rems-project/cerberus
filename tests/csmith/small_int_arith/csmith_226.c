// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_226.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 0x871C7BF0L;
static int32_t g_6 = 0x50E6DA50L;
static uint16_t g_9 = 0x9E53L;
static uint64_t g_20 = 3UL;
static uint32_t g_23 = 0x8F585950L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int8_t l_5 = 0L;
    int32_t l_7 = 0L;
    int32_t l_8 = 0L;
    int16_t l_32 = 0L;
    g_6 = ((safe_div_func_int8_t_s_s(g_4, (-2L))) & l_5);
    g_9--;
    if ((safe_mod_func_uint64_t_u_u(g_4, 0x9B950315362DAAB7LL)))
    { 
        uint16_t l_22 = 0UL;
        int32_t l_26 = 0xD0B6BD0DL;
lbl_27:
        for (l_7 = 0; (l_7 != 4); l_7 = safe_add_func_int32_t_s_s(l_7, 4))
        { 
            int32_t l_19 = (-7L);
            int32_t l_21 = 7L;
            l_21 = (~((safe_mod_func_int32_t_s_s(((g_20 = (l_19 < g_4)) && g_6), l_19)) < 0xBBL));
            g_23 = ((l_22 = (((4294967292UL != 0x01DBDAE4L) , 1UL) && 0x52L)) != 0xDF86095610A1434ALL);
            l_26 = (safe_rshift_func_uint8_t_u_s(246UL, 6));
        }
        l_26 = 0x5B01D976L;
        if (g_6)
            goto lbl_27;
    }
    else
    { 
        l_8 = 1L;
    }
    l_8 = (safe_mod_func_int8_t_s_s((safe_mod_func_int64_t_s_s((g_23 , 0L), l_7)), g_23));
    return l_32;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
