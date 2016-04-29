// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_161.c
#include "csmith.h"


static long __undefined;



static int16_t g_6 = 0x188EL;
static int8_t g_11 = (-9L);
static int32_t g_13 = 0xBEFA1E1CL;
static uint32_t g_15 = 0xCF1C946BL;
static uint32_t g_53 = 0x5F814D19L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint16_t l_4 = 0xA9C4L;
    int32_t l_5 = (-1L);
    int32_t l_7 = 0x9AAED6B6L;
    int32_t l_8 = 0L;
    int32_t l_12 = (-1L);
    int32_t l_14 = 0x1912530AL;
    l_8 = (l_7 |= ((((((l_5 ^= (safe_add_func_uint8_t_u_u(l_4, l_4))) >= 0xF8F0L) | 0xE6F7FBF2L) >= l_4) , g_6) <= 0x44A754320E32CF41LL));
    g_13 = (safe_mod_func_int32_t_s_s(((((++g_15) > (248UL | l_7)) < 0xE197E7C1L) || g_11), l_7));
    if ((+(g_15 = l_14)))
    { 
        uint8_t l_29 = 8UL;
        int32_t l_30 = (-9L);
        l_14 = (safe_sub_func_uint8_t_u_u((l_30 ^= (((safe_mod_func_uint64_t_u_u(((g_15++) ^ ((((safe_mod_func_int8_t_s_s((safe_mod_func_int16_t_s_s((g_6 , l_29), g_6)), 0xADL)) <= g_11) ^ 0x747C914AL) , 4294967295UL)), l_29)) , 0x13550E35L) , 255UL)), 255UL));
        l_30 = (g_15 || l_4);
        return g_15;
    }
    else
    { 
        int32_t l_45 = 0x8BE49C90L;
        int32_t l_51 = (-8L);
        int32_t l_52 = 0x09EDB9CCL;
        for (l_7 = 0; (l_7 <= (-22)); l_7--)
        { 
            uint8_t l_44 = 0x6BL;
            int32_t l_46 = 0x0953B224L;
            l_14 ^= ((safe_add_func_int64_t_s_s((safe_div_func_int64_t_s_s((safe_sub_func_int64_t_s_s(g_15, g_11)), l_12)), l_4)) | 255UL);
            for (l_8 = 0; (l_8 == (-4)); --l_8)
            { 
                g_13 |= 0x242EA6AEL;
                g_13 ^= (~(l_46 = (((((safe_mod_func_int32_t_s_s(g_15, l_44)) , l_45) | 0x546153B72B46FAC5LL) && g_15) || 0xE6L)));
            }
        }
        g_53 &= (((((safe_rshift_func_int16_t_s_u((l_51 &= (safe_mul_func_int8_t_s_s((((l_45 <= g_13) || l_45) <= g_15), g_13))), 15)) > 8UL) >= 4294967291UL) && g_6) , l_52);
    }
    l_7 = (((safe_div_func_int64_t_s_s((safe_add_func_int32_t_s_s((safe_add_func_uint32_t_u_u((safe_rshift_func_int8_t_s_s(((((safe_div_func_int16_t_s_s(((((l_5 = g_15) , g_53) || l_14) , l_5), l_7)) & l_4) < l_8) , g_6), 6)), g_13)), l_12)), 8UL)) , 65527UL) , 0x86565EA9L);
    return g_15;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_53, "g_53", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
