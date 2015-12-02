// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_210.c
#include "csmith.h"


static long __undefined;



static uint8_t g_15 = 0x5CL;
static uint16_t g_20 = 0x761BL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint16_t l_2 = 0xEA75L;
    int32_t l_17 = 0xAB227D37L;
    int16_t l_32 = 0x49CFL;
lbl_45:
    l_2--;
    for (l_2 = 19; (l_2 == 58); l_2 = safe_add_func_int8_t_s_s(l_2, 2))
    { 
        uint32_t l_16 = 0xC407858FL;
        int32_t l_18 = 1L;
        int8_t l_19 = (-5L);
        if ((l_17 ^= (((safe_add_func_uint32_t_u_u(((safe_lshift_func_int16_t_s_u((safe_unary_minus_func_uint16_t_u((+((((safe_mod_func_int16_t_s_s(l_2, g_15)) >= l_16) ^ 0x25L) | 0x54L)))), 11)) && 0x56890C54L), g_15)) , l_2) >= 0xA55FL)))
        { 
            int32_t l_31 = (-1L);
            int32_t l_33 = 0x81B5F7A0L;
            l_18 |= 0x373A4C92L;
            g_20 = (g_15 >= l_19);
            l_33 = (l_18 &= ((safe_rshift_func_int16_t_s_s((((l_31 = (safe_lshift_func_int8_t_s_u((safe_lshift_func_uint8_t_u_s((((safe_mul_func_int8_t_s_s((safe_rshift_func_uint8_t_u_s(7UL, 0)), g_15)) ^ 0x46B5L) || l_17), l_2)), 3))) != l_32) <= 0x9CL), g_15)) | 0xCDC0F1FAL));
            l_31 ^= (!(~(safe_lshift_func_int16_t_s_u((safe_lshift_func_int16_t_s_u((!(safe_mul_func_uint16_t_u_u((((safe_mod_func_uint64_t_u_u((((0x11F64DB2L == g_20) == 0x64L) , l_16), g_20)) | g_20) , l_33), 0x45CBL))), 9)), l_19))));
        }
        else
        { 
            l_18 = l_17;
        }
        if (l_16)
            continue;
        if (g_15)
            goto lbl_45;
    }
    return l_17;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
