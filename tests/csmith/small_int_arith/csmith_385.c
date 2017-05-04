// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_385.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static uint64_t g_6 = 0xB5725D36729694D2LL;
static int8_t g_7 = 0xB8L;
static int64_t g_10 = (-1L);
static uint64_t g_27 = 0xD402A53EBFF7828ELL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int32_t l_3 = (-2L);
    int32_t l_4 = 0xC3707822L;
    int8_t l_5 = 4L;
    int8_t l_28 = 0x9DL;
    l_3 = g_2;
lbl_29:
    g_2 = ((((((l_4 = g_2) < 0x7FL) <= 1L) == g_2) < 0xB8L) | l_5);
    if ((g_7 &= (l_4 = (g_6 &= (((((g_2 , l_3) == 0x5A9864BA8B35EDADLL) , l_5) || g_2) ^ l_4)))))
    { 
        uint32_t l_21 = 0x394A737BL;
        g_10 ^= ((((safe_lshift_func_uint8_t_u_u((l_5 < g_2), 4)) ^ 0x39523DD972C40A98LL) & g_2) >= g_6);
        g_2 = ((((safe_div_func_int64_t_s_s((safe_add_func_int64_t_s_s((l_4 = (((safe_mul_func_uint16_t_u_u(((safe_mul_func_int8_t_s_s((safe_add_func_uint16_t_u_u(((g_7 , 0x1C57511EL) | g_2), 0x9C2BL)), 1UL)) & g_6), 0xBDD8L)) , l_3) ^ g_2)), 7UL)), 3L)) , l_4) && 0xF7DCL) , g_6);
        l_21--;
    }
    else
    { 
        int16_t l_26 = 0x0DECL;
        g_27 &= ((safe_rshift_func_uint16_t_u_s(((((g_2 < (-1L)) == g_2) , l_4) , 3UL), l_26)) && l_4);
        g_2 = 9L;
        l_28 = l_5;
        return l_28;
    }
    if (l_28)
        goto lbl_29;
    return g_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
