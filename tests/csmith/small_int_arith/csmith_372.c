// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_372.c
#include "csmith.h"


static long __undefined;



static int32_t g_11 = 1L;
static int16_t g_15 = (-1L);
static uint32_t g_16 = 4294967290UL;
static uint32_t g_26 = 0x6C0B333EL;
static int64_t g_27 = 0xF6A08376FBFCC013LL;
static int32_t g_35 = 0x4A2C6EB8L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint32_t l_10 = 0xEA41449CL;
    int32_t l_48 = 0xA7B48FE2L;
    if (((safe_mod_func_uint16_t_u_u((safe_lshift_func_int8_t_s_u(((safe_rshift_func_int8_t_s_s((safe_lshift_func_int16_t_s_u(((l_10 < g_11) | l_10), 12)), g_11)) | g_11), 7)), l_10)) == g_11))
    { 
        uint64_t l_12 = 0xC3EC3D4E703026D8LL;
        uint8_t l_34 = 1UL;
        --l_12;
        --g_16;
        if ((((safe_add_func_int16_t_s_s(3L, 1L)) & l_12) >= g_16))
        { 
            int8_t l_21 = 0xC9L;
            l_21 = g_15;
            g_27 = ((g_26 = (((safe_lshift_func_int8_t_s_u((safe_div_func_uint64_t_u_u(g_11, g_11)), l_10)) , 0x19FAL) & l_21)) == l_12);
            for (l_12 = 0; (l_12 != 40); l_12 = safe_add_func_uint16_t_u_u(l_12, 2))
            { 
                g_35 = (((((safe_mod_func_uint16_t_u_u(((safe_lshift_func_uint16_t_u_s((l_34 , 65534UL), g_27)) > g_15), 65535UL)) == l_21) >= l_10) ^ g_27) , l_12);
                g_35 = l_34;
                return g_15;
            }
        }
        else
        { 
            uint16_t l_44 = 1UL;
            g_35 = ((safe_add_func_uint8_t_u_u((safe_rshift_func_uint8_t_u_u((safe_lshift_func_uint8_t_u_u(((safe_mul_func_uint8_t_u_u(0UL, l_44)) < l_12), l_34)), g_26)), g_35)) & (-1L));
        }
    }
    else
    { 
        uint32_t l_45 = 1UL;
lbl_51:
        l_45 = g_11;
        for (g_15 = (-21); (g_15 == 24); ++g_15)
        { 
            return l_48;
        }
        for (l_45 = (-22); (l_45 == 42); l_45 = safe_add_func_uint8_t_u_u(l_45, 7))
        { 
            if (l_45)
                goto lbl_51;
        }
    }
    return g_15;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
