// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o gen/csmith_02.c
#include "csmith.h"


static long __undefined;



static uint8_t g_3 = 0xF2L;
static uint32_t g_22 = 0UL;
static uint32_t g_38 = 0x9C36C1D6L;
static int16_t g_47 = (-1L);



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint32_t l_2 = 0x7E8EDF1FL;
    int32_t l_6 = 1L;
    uint8_t l_29 = 2UL;
    int8_t l_48 = 0xCCL;
    g_3 = l_2;
    l_6 = ((safe_sub_func_uint64_t_u_u(g_3, l_2)) , 0x4351CDCBL);
    if (g_3)
    { 
        for (g_3 = 0; (g_3 <= 24); g_3++)
        { 
            l_6 = (-1L);
        }
    }
    else
    { 
        uint32_t l_21 = 0xA07C694AL;
        uint64_t l_23 = 1UL;
        int32_t l_26 = 1L;
lbl_39:
        for (l_6 = 0; (l_6 > 27); l_6 = safe_add_func_int32_t_s_s(l_6, 6))
        { 
            if (g_3)
                break;
        }
        if ((l_6 = (((safe_rshift_func_uint16_t_u_u((safe_sub_func_uint16_t_u_u((safe_rshift_func_uint16_t_u_s((((safe_sub_func_uint64_t_u_u(((safe_div_func_int8_t_s_s(l_21, l_21)) || l_2), 0UL)) == 0xEAB1D6A56C37FC05LL) || l_2), g_3)), g_22)), g_3)) , l_6) , l_23)))
        { 
            int32_t l_25 = 1L;
            uint32_t l_30 = 0UL;
            l_6 ^= (~(l_26 &= l_25));
            l_30 ^= ((l_29 = (((safe_sub_func_int8_t_s_s((-1L), g_3)) & g_3) <= g_22)) , 0x6A4ABFF1L);
        }
        else
        { 
            uint16_t l_36 = 0x07ADL;
            int32_t l_37 = 0x205E60D1L;
            g_38 = (l_37 ^= (((safe_mul_func_int16_t_s_s((safe_div_func_uint8_t_u_u((g_3 = (!0UL)), 0xDAL)), (-1L))) , g_22) >= l_36));
            if (l_2)
                goto lbl_39;
        }
        for (l_2 = (-22); (l_2 > 37); ++l_2)
        { 
            for (g_38 = 29; (g_38 <= 13); g_38 = safe_sub_func_uint16_t_u_u(g_38, 9))
            { 
                int32_t l_46 = 0x43993911L;
                g_47 |= ((safe_add_func_uint32_t_u_u(0x94902820L, l_46)) , 1L);
            }
            return l_23;
        }
    }
    return l_48;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    transparent_crc(g_47, "g_47", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
