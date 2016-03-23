// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_290.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static uint32_t g_26 = 0xBA87A5EAL;
static uint16_t g_27 = 65535UL;
static int16_t g_28 = (-7L);
static uint64_t g_30 = 0UL;
static int64_t g_59 = 0xDF642D94904418F7LL;
static uint32_t g_60 = 0x9F010208L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint32_t l_9 = 0xE1C97412L;
    int32_t l_24 = 0L;
    int32_t l_25 = (-9L);
lbl_33:
    for (g_2 = (-28); (g_2 == (-26)); g_2 = safe_add_func_int32_t_s_s(g_2, 6))
    { 
        uint32_t l_7 = 0xDB34E6D4L;
        int32_t l_8 = 0xA07E4FC2L;
        l_8 |= (safe_sub_func_uint16_t_u_u(((l_7 = 0L) , 0x887CL), g_2));
        l_9 ^= (g_2 , g_2);
    }
    if ((((safe_div_func_uint16_t_u_u((safe_mul_func_int16_t_s_s((safe_mod_func_int32_t_s_s(((g_27 = (safe_lshift_func_int8_t_s_u(((g_26 ^= (safe_add_func_int8_t_s_s((l_25 = (+(l_24 = ((safe_div_func_uint64_t_u_u(((+g_2) | g_2), l_9)) == 0xCD2466E9L)))), l_9))) != 1UL), l_9))) , 5L), (-2L))), l_9)), g_2)) , l_25) ^ l_9))
    { 
        int8_t l_29 = 1L;
        g_30--;
    }
    else
    { 
        uint64_t l_34 = 0xBBFAD0D7276CC72BLL;
        int32_t l_35 = 0L;
        int32_t l_50 = 0xBDE8AFF6L;
        if (l_9)
            goto lbl_33;
        if (l_34)
        { 
            uint8_t l_36 = 9UL;
            int32_t l_43 = 0x5E0C0A10L;
            l_36--;
            l_43 = (safe_mod_func_uint64_t_u_u(((--g_26) > l_9), g_27));
            g_2 = (l_43 &= ((g_30 && 0xD8L) , g_26));
            l_50 |= (((safe_rshift_func_int8_t_s_u((safe_sub_func_int16_t_s_s((l_35 = (safe_add_func_uint64_t_u_u(18446744073709551611UL, (-9L)))), 0x3C7DL)), l_43)) | g_28) != 0xF4FCL);
        }
        else
        { 
            l_50 &= (safe_lshift_func_int16_t_s_s((+(safe_mod_func_int8_t_s_s((((safe_rshift_func_int16_t_s_u((+g_27), 1)) | 1UL) != g_30), 1L))), 13));
            l_50 = (((g_27 = 0x64C1L) == g_30) <= g_28);
        }
        g_60--;
        g_2 ^= (safe_div_func_int64_t_s_s(l_9, l_34));
    }
    return g_26;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    transparent_crc(g_59, "g_59", print_hash_value);
    transparent_crc(g_60, "g_60", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
