// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_064.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 0xA136951AL;
static int64_t g_9 = 0x61ECE3051EBF0DDDLL;
static int8_t g_10 = 0L;
static int16_t g_26 = 0x98DCL;
static uint32_t g_38 = 0xA84ADE72L;
static uint16_t g_39 = 65535UL;
static int16_t g_40 = 0L;
static uint32_t g_56 = 6UL;
static uint32_t g_57 = 0x1506F573L;
static int16_t g_59 = 0xDFA8L;
static uint16_t g_61 = 0xA623L;
static uint32_t g_66 = 0UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint64_t l_5 = 0x53BC6E5C7A00F47ALL;
    uint64_t l_29 = 0x3ED13222C7E12FD8LL;
    uint16_t l_30 = 0x98BBL;
    int32_t l_52 = (-1L);
    int32_t l_60 = 0x1B5B3A04L;
    if ((safe_div_func_int8_t_s_s((g_4 != l_5), g_4)))
    { 
        uint64_t l_6 = 0xD3F5047C4D1454BCLL;
        l_6 = ((g_4 , 0x0D72276B87D0FA51LL) ^ 18446744073709551615UL);
        for (g_4 = (-18); (g_4 == 43); ++g_4)
        { 
            if (g_4)
                break;
            g_9 ^= g_4;
        }
        return g_9;
    }
    else
    { 
        uint32_t l_37 = 18446744073709551615UL;
        int32_t l_47 = 0L;
        if ((g_10 = 0L))
        { 
            uint16_t l_27 = 0xA3FDL;
            int32_t l_28 = 3L;
            int32_t l_58 = 0xB1956A74L;
lbl_53:
            for (g_4 = 11; (g_4 < 6); --g_4)
            { 
                int32_t l_25 = 6L;
                l_30 ^= (safe_lshift_func_uint16_t_u_s(((safe_add_func_int16_t_s_s(((safe_add_func_int32_t_s_s(((!(safe_mod_func_int16_t_s_s(((!(l_27 ^= ((g_26 = (((safe_div_func_uint64_t_u_u(l_5, l_25)) && 0x1521FAFBL) <= 1UL)) < 0x63372585L))) > g_4), g_9))) == g_10), 0xAA50887CL)) , 0x6A81L), l_28)) , l_25), l_29));
                g_38 = (safe_lshift_func_uint8_t_u_s((safe_mod_func_int32_t_s_s(((safe_lshift_func_int8_t_s_u(((1UL | l_25) == 0x59L), 7)) == l_37), 0x506946CBL)), 7));
            }
            if (g_39)
            { 
                int64_t l_50 = (-8L);
                uint16_t l_51 = 0x74B4L;
                g_40 ^= (l_28 = g_4);
                l_47 = (safe_unary_minus_func_int8_t_s(((+(safe_mod_func_uint8_t_u_u(((safe_mul_func_uint16_t_u_u(g_9, l_28)) ^ 6L), 0x78L))) | 0x94L)));
                l_28 &= ((((safe_add_func_uint8_t_u_u(l_50, 0xD5L)) <= 0L) > 0xB6L) ^ g_40);
                l_52 = (l_51 > 0x6D9140931BC1F9C8LL);
            }
            else
            { 
                if (l_30)
                    goto lbl_53;
            }
            g_57 = (safe_div_func_uint8_t_u_u(((g_56 = l_52) || 0x88F5L), l_47));
            g_61++;
        }
        else
        { 
            int8_t l_64 = 0x77L;
            int32_t l_65 = 0x95732B80L;
            l_47 |= (g_38 >= l_64);
            l_65 |= g_57;
        }
    }
    ++g_66;
    return l_30;
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
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    transparent_crc(g_39, "g_39", print_hash_value);
    transparent_crc(g_40, "g_40", print_hash_value);
    transparent_crc(g_56, "g_56", print_hash_value);
    transparent_crc(g_57, "g_57", print_hash_value);
    transparent_crc(g_59, "g_59", print_hash_value);
    transparent_crc(g_61, "g_61", print_hash_value);
    transparent_crc(g_66, "g_66", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
