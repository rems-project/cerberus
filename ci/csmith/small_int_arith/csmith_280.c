// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_280.c
#include "csmith.h"


static long __undefined;



static int32_t g_9 = 0x75EE4C20L;
static int32_t g_11 = 0xE5034859L;
static int16_t g_12 = 0x0552L;
static int64_t g_13 = 0L;
static uint64_t g_15 = 0x35DA2A0C0E075257LL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint8_t l_4 = 0x80L;
    uint16_t l_5 = 1UL;
    uint32_t l_6 = 0x48B1647CL;
    int8_t l_7 = (-8L);
    int32_t l_8 = 3L;
    int16_t l_10 = 0x9CC0L;
    int32_t l_14 = 0x7153413FL;
    int8_t l_46 = 0x8FL;
    l_8 = ((((((safe_rshift_func_uint16_t_u_s(((((((l_4 = (-10L)) || l_5) , l_5) , 0xA92BL) <= 0xA8CDL) || 0xAE7BL), l_6)) ^ l_5) ^ l_6) , l_5) ^ l_7) <= 0UL);
    --g_15;
    l_8 = g_13;
    for (l_14 = (-22); (l_14 != (-7)); l_14 = safe_add_func_uint64_t_u_u(l_14, 9))
    { 
        uint32_t l_26 = 4294967286UL;
        uint8_t l_43 = 0x0DL;
        for (l_10 = 0; (l_10 > (-3)); l_10 = safe_sub_func_int16_t_s_s(l_10, 8))
        { 
            uint32_t l_22 = 0xA2589D38L;
            int32_t l_33 = (-1L);
            if ((l_22 <= g_15))
            { 
                int32_t l_23 = 0x7BC6200DL;
                uint8_t l_42 = 2UL;
                if ((1UL | g_15))
                { 
                    l_23 |= g_15;
                }
                else
                { 
                    int8_t l_27 = 0xDCL;
                    int32_t l_28 = 0x2CBD4DAEL;
                    if (((((safe_div_func_int8_t_s_s(g_15, l_26)) == l_27) & 0x32L) != l_28))
                    { 
                        uint64_t l_29 = 0x6E16511C25C5395FLL;
                        int32_t l_30 = 0xD8AC507BL;
                        l_30 &= l_29;
                        g_11 = (safe_mul_func_int16_t_s_s(0L, 0x29ADL));
                    }
                    else
                    { 
                        l_33 &= 0L;
                        return g_9;
                    }
                }
                l_8 ^= (safe_mul_func_uint16_t_u_u((safe_add_func_uint16_t_u_u((safe_mul_func_int16_t_s_s((((safe_div_func_uint32_t_u_u(4294967295UL, g_9)) | l_42) > l_43), l_23)), l_33)), 0x5A02L));
                for (l_8 = 14; (l_8 >= (-15)); l_8--)
                { 
                    g_9 &= (g_11 = ((l_26 ^ 0xB54AL) <= 0UL));
                }
                l_46 = (l_33 = l_43);
            }
            else
            { 
                return g_9;
            }
            g_9 = g_12;
            l_8 = ((((((l_7 != l_22) , g_13) ^ 0x1945B4E6L) , 0x1A91F101L) ^ g_13) , 0x815809F1L);
        }
        if (l_5)
            break;
        if (g_13)
            continue;
    }
    return g_13;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
