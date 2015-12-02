// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_200.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static uint32_t g_3 = 4294967295UL;
static int64_t g_4 = 0xDDD3F46721591249LL;
static uint64_t g_9 = 0x98CAFA32FD2D1A4ELL;
static int32_t g_16 = (-6L);
static uint8_t g_17 = 0x56L;
static uint64_t g_22 = 0xE6C0B333EE676845LL;
static int16_t g_38 = 7L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int16_t l_5 = 7L;
    int32_t l_7 = 0xB6BC3EC3L;
    int32_t l_33 = 3L;
    if (((-1L) | g_2))
    { 
        int64_t l_6 = (-6L);
        int32_t l_8 = 0x30377367L;
        int64_t l_21 = 0L;
lbl_18:
        g_4 = (g_3 = g_2);
        l_5 = (g_4 == g_4);
        if (((l_7 = (l_5 <= l_6)) || l_6))
        { 
            g_9++;
        }
        else
        { 
            uint32_t l_12 = 1UL;
            l_12 &= g_4;
            for (l_5 = (-2); (l_5 == (-23)); l_5--)
            { 
                int32_t l_15 = 0xAEBA4D3EL;
                uint32_t l_39 = 0xC387C7A5L;
                g_16 &= l_15;
                if (((g_17 |= l_7) | (-1L)))
                { 
                    if (l_15)
                        goto lbl_18;
                    for (l_15 = 0; (l_15 <= 28); l_15 = safe_add_func_int64_t_s_s(l_15, 2))
                    { 
                        g_22 &= l_21;
                    }
                }
                else
                { 
                    int8_t l_32 = 0xB1L;
                    l_7 |= 0x08376FBFL;
                    for (l_7 = (-8); (l_7 != (-3)); l_7++)
                    { 
                        uint8_t l_25 = 0x89L;
                        l_25 = (-8L);
                        l_33 = (safe_sub_func_int16_t_s_s(((safe_mod_func_int64_t_s_s(((safe_div_func_int32_t_s_s((((l_12 && g_3) == l_8) <= l_32), g_9)) & (-1L)), g_3)) ^ g_17), 0xA5FCL));
                    }
                }
                l_8 = ((((safe_rshift_func_uint8_t_u_s((g_38 ^= (--g_17)), (l_7 |= 0x88L))) != 0xEAE8L) & 18446744073709551610UL) , l_39);
            }
        }
    }
    else
    { 
        int8_t l_40 = 0xFFL;
        l_40 = 0x9124C6E1L;
    }
    return l_33;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
