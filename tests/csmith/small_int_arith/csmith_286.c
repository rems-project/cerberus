// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_286.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 0x1A04L;
static int8_t g_7 = 9L;
static uint16_t g_17 = 0UL;
static int16_t g_21 = 3L;
static int64_t g_26 = 0x857B1A094951162DLL;
static int32_t g_36 = 0x50C19791L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int16_t l_5 = 0x768CL;
    uint32_t l_8 = 0xA2A3B3F3L;
    int32_t l_14 = 1L;
    uint16_t l_42 = 0x9DB2L;
    ++g_2;
    if (((g_2 ^ (-4L)) && l_5))
    { 
        int32_t l_6 = 1L;
        l_8++;
    }
    else
    { 
        uint64_t l_13 = 18446744073709551606UL;
lbl_20:
        l_14 = (((safe_lshift_func_int8_t_s_u(l_13, 0)) != l_13) , g_7);
        l_14 &= 0xEF5D870AL;
        for (l_13 = 3; (l_13 <= 55); l_13 = safe_add_func_uint16_t_u_u(l_13, 4))
        { 
            ++g_17;
            if (l_14)
                goto lbl_20;
            g_21 = l_13;
        }
    }
    l_14 = ((((safe_sub_func_uint32_t_u_u(l_14, 3L)) , l_8) | 0xB384L) ^ g_2);
    if (((safe_sub_func_uint16_t_u_u(g_21, l_14)) == 0xC6L))
    { 
        uint32_t l_39 = 0xD47CDD53L;
        if (((g_17 , g_7) == 0xCAA5L))
        { 
            uint64_t l_29 = 0x309AB83EB61943ECLL;
            g_26 |= (l_5 , 2L);
            for (g_2 = 0; (g_2 >= 29); g_2 = safe_add_func_uint8_t_u_u(g_2, 2))
            { 
                l_29++;
                g_36 = ((safe_rshift_func_uint16_t_u_u((safe_div_func_int16_t_s_s(g_17, 1UL)), 7)) >= g_26);
            }
        }
        else
        { 
            g_36 = ((g_7 = (safe_add_func_int16_t_s_s(g_7, 0xF7D5L))) ^ 1L);
            l_14 = 1L;
        }
        g_36 = (0x32215F8FL == l_39);
    }
    else
    { 
        uint8_t l_40 = 1UL;
        int32_t l_41 = 4L;
        g_36 |= (0xA36FE543L < l_40);
        --l_42;
        l_14 &= (safe_mul_func_int8_t_s_s(((safe_unary_minus_func_uint8_t_u((safe_mul_func_int8_t_s_s((0x4E4A53E8AF80453DLL >= l_42), 8L)))) | (-1L)), g_17));
    }
    return g_36;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_36, "g_36", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
