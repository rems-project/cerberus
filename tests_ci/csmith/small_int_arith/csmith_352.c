// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_352.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0UL;
static uint64_t g_3 = 0xF98A59C17633EFC0LL;
static int32_t g_6 = 0x2CA3C0BFL;
static uint64_t g_11 = 18446744073709551608UL;
static int32_t g_32 = (-1L);
static uint8_t g_39 = 4UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int32_t l_4 = 0x4EBB0CB8L;
    int32_t l_26 = 0L;
    int32_t l_38 = 0x1021F5EBL;
    g_3 ^= (g_2 && 2UL);
    if ((l_4 > 0UL))
    { 
        int16_t l_16 = 0x4CF5L;
lbl_35:
        g_6 = (safe_unary_minus_func_int32_t_s(0x2A149CECL));
        for (g_2 = 4; (g_2 <= 44); g_2++)
        { 
            int64_t l_25 = 1L;
            g_11 |= (safe_rshift_func_uint16_t_u_u(g_6, g_6));
            g_6 = 0x7525D2D9L;
            if (((safe_mul_func_int16_t_s_s((safe_add_func_int8_t_s_s(l_16, g_3)), l_16)) && g_3))
            { 
                int32_t l_19 = 0x658A6001L;
                g_6 ^= g_2;
                g_6 ^= (safe_mul_func_int8_t_s_s(0xCBL, 0x1AL));
                l_19 &= (0UL != 0x5EBDA184L);
            }
            else
            { 
                uint64_t l_24 = 0xA3BDF78B15B45BEALL;
                if (g_2)
                    break;
                l_26 = (((((safe_mod_func_uint32_t_u_u((safe_sub_func_int32_t_s_s((l_4 > l_16), l_4)), l_16)) || l_24) | l_16) == 0x65L) == l_25);
                for (l_26 = (-28); (l_26 < (-15)); ++l_26)
                { 
                    if (l_26)
                        break;
                    g_32 |= ((safe_add_func_uint64_t_u_u(((safe_unary_minus_func_uint32_t_u(((((0x325CF162C80F3BBALL < 18446744073709551615UL) , g_3) , l_4) != g_6))) <= 0x6EL), l_24)) || 0x0FL);
                    for (g_3 = 4; (g_3 > 12); g_3++)
                    { 
                        if (l_24)
                            goto lbl_35;
                        return g_2;
                    }
                }
            }
        }
        l_26 &= (((safe_mod_func_int8_t_s_s(l_16, g_3)) >= l_16) >= 0xFCE24956L);
    }
    else
    { 
        g_39++;
    }
    l_26 = (safe_div_func_uint64_t_u_u(0x02EEDA7DA9FC5C2DLL, 18446744073709551613UL));
    return g_11;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_32, "g_32", print_hash_value);
    transparent_crc(g_39, "g_39", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
