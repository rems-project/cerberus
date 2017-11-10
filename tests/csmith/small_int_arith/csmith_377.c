// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_377.c
#include "csmith.h"


static long __undefined;



static int32_t g_4 = 4L;
static int32_t g_9 = 0x16A205B2L;
static uint8_t g_10 = 255UL;
static int8_t g_18 = (-10L);
static uint16_t g_20 = 65527UL;
static uint8_t g_32 = 5UL;
static int32_t g_35 = 0x3BE41B0CL;
static uint8_t g_36 = 0x1BL;
static int32_t g_46 = 0L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_2 = 6L;
    int32_t l_19 = (-1L);
    int32_t l_45 = (-3L);
    int8_t l_52 = 0L;
    uint8_t l_53 = 255UL;
    if ((1L < l_2))
    { 
        int32_t l_3 = (-5L);
        int32_t l_8 = 0x5165352FL;
        int32_t l_17 = 1L;
        l_3 ^= (-1L);
        if (g_4)
        { 
            int32_t l_7 = 0x65E08CCCL;
            l_7 = (safe_mod_func_uint32_t_u_u(g_4, 4294967293UL));
            g_10--;
            l_17 ^= ((safe_add_func_uint8_t_u_u(((safe_lshift_func_int16_t_s_s(l_8, 9)) , 254UL), l_7)) , (-8L));
        }
        else
        { 
            int64_t l_23 = 0x4129B85755261FC4LL;
            int8_t l_24 = 0x02L;
            int32_t l_30 = 0x082F4E55L;
            int32_t l_31 = 0x0336D065L;
            g_20--;
            if ((((g_9 , l_23) , g_10) , l_24))
            { 
                uint16_t l_27 = 1UL;
                int32_t l_28 = 0L;
                int32_t l_29 = 1L;
                l_27 ^= (0x3BF118C84B7B8319LL ^ 0L);
                g_32++;
                g_36--;
            }
            else
            { 
                g_4 &= ((safe_sub_func_uint32_t_u_u(g_10, g_9)) && 0x1B70L);
            }
lbl_43:
            g_9 |= 0x84EDB553L;
            for (g_35 = 0; (g_35 <= (-5)); g_35 = safe_sub_func_int64_t_s_s(g_35, 8))
            { 
                uint16_t l_47 = 7UL;
                if (l_17)
                    goto lbl_43;
                l_47 |= (g_4 = ((g_46 = ((safe_unary_minus_func_uint16_t_u(((l_45 && 5L) , g_4))) < l_45)) == l_45));
            }
        }
        l_19 ^= 0L;
        for (g_18 = 0; (g_18 == 8); ++g_18)
        { 
            if (g_20)
                break;
            g_9 = g_20;
            l_8 |= ((((safe_sub_func_uint16_t_u_u(0xD0ABL, l_52)) , g_32) & 0xF39980A6F85D55A9LL) != l_45);
        }
    }
    else
    { 
        ++l_53;
    }
    for (g_36 = 0; (g_36 >= 11); g_36 = safe_add_func_int64_t_s_s(g_36, 8))
    { 
        g_9 ^= 0xE5AB8BF5L;
    }
    return l_45;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_32, "g_32", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    transparent_crc(g_36, "g_36", print_hash_value);
    transparent_crc(g_46, "g_46", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
