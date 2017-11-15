// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_028.c
#include "csmith.h"


static long __undefined;



static uint8_t g_3 = 0x3CL;
static uint64_t g_7 = 0xDAAB72B21A35CA42LL;
static uint8_t g_8 = 0xF1L;
static int32_t g_13 = 0x4CCFD66CL;
static uint8_t g_25 = 255UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int32_t l_2 = 2L;
    int32_t l_6 = (-5L);
    int32_t l_23 = (-1L);
    uint64_t l_24 = 0x6DABAC8EF34EA885LL;
    g_3 = (((l_2 , l_2) <= 1UL) , 0x92443250L);
    g_7 |= (l_6 |= ((safe_rshift_func_int16_t_s_u(1L, l_2)) | l_2));
    g_8--;
    if ((safe_add_func_uint8_t_u_u((0x637C1D6BL & 0xB0A3531FL), l_6)))
    { 
        return g_8;
    }
    else
    { 
        uint16_t l_14 = 5UL;
        g_13 = (-9L);
        if (l_14)
        { 
            int16_t l_22 = 0x8595L;
            l_23 = (safe_mul_func_int8_t_s_s(((safe_rshift_func_uint16_t_u_s(((l_6 = ((safe_lshift_func_int8_t_s_u(((((!l_14) | g_8) > 0x14L) , l_22), l_22)) || g_8)) ^ g_8), 4)) , 0x1DL), l_2));
            l_24 = (g_13 || 0x7440L);
        }
        else
        { 
            g_25++;
        }
    }
    return l_23;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
