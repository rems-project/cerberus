// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_056.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static int32_t g_20 = 0x7F8B4DFEL;
static int32_t g_32 = 6L;
static int16_t g_33 = 9L;
static int16_t g_38 = 0xBB32L;
static uint32_t g_40 = 18446744073709551614UL;
static int64_t g_43 = (-1L);
static uint64_t g_44 = 18446744073709551608UL;
static uint64_t g_57 = 18446744073709551613UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_5 = 0x9F4288A1L;
    int32_t l_31 = (-3L);
    int32_t l_34 = (-1L);
    int32_t l_35 = 0x8264D924L;
    int32_t l_36 = 7L;
    int32_t l_37 = 6L;
    int32_t l_39 = 0xEEE83ADEL;
lbl_21:
    for (g_2 = 0; (g_2 > 8); ++g_2)
    { 
        int32_t l_18 = 0x32AA61FCL;
        int32_t l_19 = 0x58900FDBL;
        ++l_5;
        if (g_2)
            continue;
        if (g_2)
            goto lbl_21;
        g_20 = ((safe_add_func_int32_t_s_s(((((safe_mul_func_int8_t_s_s(((safe_mul_func_int8_t_s_s((((safe_add_func_uint8_t_u_u((l_18 |= (safe_mul_func_uint8_t_u_u(0xB0L, g_2))), 255UL)) >= l_19) >= 18446744073709551615UL), g_2)) > l_19), l_19)) & 1L) ^ l_19) & g_2), g_2)) | 0UL);
    }
    if (g_20)
    { 
        uint64_t l_24 = 0x6F39384257392715LL;
        int32_t l_25 = 6L;
        l_25 |= (safe_mul_func_int16_t_s_s(l_24, g_2));
    }
    else
    { 
        for (g_2 = 0; (g_2 <= 0); ++g_2)
        { 
            int8_t l_28 = 0xEDL;
            g_20 = l_28;
        }
        for (g_2 = (-13); (g_2 >= 29); g_2++)
        { 
            l_31 |= l_5;
        }
        g_40++;
    }
    g_44--;
    for (g_32 = 0; (g_32 < (-11)); g_32--)
    { 
        int32_t l_51 = 0L;
        l_51 ^= (((safe_mod_func_int32_t_s_s((l_31 | l_5), g_44)) , 18446744073709551613UL) , g_43);
        l_51 = g_38;
        for (g_38 = 4; (g_38 >= 16); ++g_38)
        { 
            uint16_t l_54 = 0UL;
            l_51 &= ((g_38 != 0x4FE605A42069719ELL) < l_54);
            for (g_20 = 0; (g_20 == (-14)); g_20 = safe_sub_func_uint16_t_u_u(g_20, 1))
            { 
                g_57++;
            }
            return g_33;
        }
        return g_38;
    }
    return g_57;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_32, "g_32", print_hash_value);
    transparent_crc(g_33, "g_33", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    transparent_crc(g_40, "g_40", print_hash_value);
    transparent_crc(g_43, "g_43", print_hash_value);
    transparent_crc(g_44, "g_44", print_hash_value);
    transparent_crc(g_57, "g_57", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
