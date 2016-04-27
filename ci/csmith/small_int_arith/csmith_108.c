// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_108.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = 0x17L;
static int32_t g_4 = 3L;
static uint32_t g_6 = 0x45D811F0L;
static int64_t g_11 = 0xE0566A927213EC75LL;
static int32_t g_30 = 0xC0105807L;
static int32_t g_32 = 1L;
static uint64_t g_45 = 0x0538E0EA626AECE0LL;
static int16_t g_46 = 0x3541L;
static uint32_t g_49 = 0x4E194E40L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int16_t l_3 = 0x838AL;
    int32_t l_5 = 0x22B16580L;
    uint8_t l_20 = 9UL;
    uint32_t l_29 = 1UL;
    l_3 = g_2;
    l_5 = ((++g_6) ^ ((safe_sub_func_uint32_t_u_u(g_4, 0UL)) < 0xD44AD374L));
    g_11 = 2L;
    if (((safe_rshift_func_uint16_t_u_u((safe_rshift_func_uint8_t_u_s((65530UL || 0xFD9DL), l_5)), g_11)) >= 0xF9B6917AB6DAD816LL))
    { 
        uint8_t l_21 = 4UL;
        int32_t l_22 = 0xF5A260DFL;
        uint8_t l_31 = 0xECL;
        uint8_t l_56 = 255UL;
        l_22 = (l_21 = (safe_add_func_uint8_t_u_u(((safe_rshift_func_uint16_t_u_s(((5L <= 0xD067L) ^ g_6), l_5)) && l_20), l_3)));
        for (l_20 = 0; (l_20 <= 21); l_20++)
        { 
            int64_t l_27 = (-1L);
            int32_t l_28 = 0x230B63E9L;
            if ((l_29 = (safe_rshift_func_int8_t_s_s((l_28 = l_27), l_21))))
            { 
                g_30 = 1L;
                l_28 |= ((g_32 = ((g_11 & g_30) , l_31)) && g_30);
                g_30 = g_6;
            }
            else
            { 
                uint8_t l_47 = 255UL;
                uint16_t l_48 = 0xB602L;
                g_30 ^= ((safe_rshift_func_int16_t_s_s((safe_mod_func_int16_t_s_s(((safe_mod_func_uint64_t_u_u((safe_add_func_uint64_t_u_u((((safe_sub_func_uint64_t_u_u((g_46 |= ((g_45 = (safe_rshift_func_int16_t_s_s((g_32 , g_32), 8))) & 5L)), l_47)) , 1UL) , l_48), g_4)), 3L)) ^ 0x585C2C10L), g_4)), l_5)) ^ l_22);
                if (((1UL > l_47) , (-7L)))
                { 
                    return g_6;
                }
                else
                { 
                    if (l_27)
                        break;
                    g_49--;
                    if (l_5)
                        continue;
                    if (l_48)
                        break;
                }
                l_5 = 0x0E5E2E4BL;
                l_28 = (safe_rshift_func_uint8_t_u_s((((safe_mul_func_uint8_t_u_u(g_46, g_46)) | l_56) , g_46), 5));
            }
        }
        g_30 = g_2;
        g_30 = ((-1L) >= g_2);
    }
    else
    { 
        g_30 ^= 6L;
    }
    return g_46;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    transparent_crc(g_32, "g_32", print_hash_value);
    transparent_crc(g_45, "g_45", print_hash_value);
    transparent_crc(g_46, "g_46", print_hash_value);
    transparent_crc(g_49, "g_49", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
