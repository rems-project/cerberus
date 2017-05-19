// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_309.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = 0x60L;
static uint64_t g_3 = 0x632667A876E6BACDLL;
static uint16_t g_14 = 65535UL;
static uint32_t g_24 = 0x401D933BL;
static uint8_t g_32 = 1UL;
static uint64_t g_46 = 0xA916C6C9A4A91A3DLL;
static int32_t g_47 = (-1L);
static uint64_t g_48 = 18446744073709551615UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int16_t l_4 = 0x4469L;
    int32_t l_9 = 0x6507E673L;
    l_4 = (g_3 = g_2);
    for (l_4 = 3; (l_4 >= (-27)); l_4 = safe_sub_func_uint8_t_u_u(l_4, 5))
    { 
        int64_t l_10 = 8L;
        int32_t l_11 = 0xA4DF6F97L;
        for (g_3 = 0; (g_3 <= 43); g_3 = safe_add_func_uint64_t_u_u(g_3, 5))
        { 
            l_9 = g_3;
            if (l_10)
                break;
        }
        if (g_3)
            break;
        l_11 = ((0L & 0xD9L) == 0x66C619A8L);
        g_14 ^= (safe_rshift_func_uint16_t_u_u(g_2, l_4));
    }
    if ((safe_unary_minus_func_uint64_t_u((((safe_mul_func_int8_t_s_s(0xB7L, 1UL)) , 1L) || g_14))))
    { 
        uint32_t l_25 = 0xE10D32DEL;
        int32_t l_30 = 0x963F6D1DL;
        for (l_4 = 11; (l_4 == 0); l_4 = safe_sub_func_int8_t_s_s(l_4, 5))
        { 
            int16_t l_31 = 0x4D41L;
            l_25 = ((safe_mul_func_uint16_t_u_u((safe_sub_func_int32_t_s_s(((g_24 = g_2) && 0x8EL), g_14)), g_2)) < g_14);
            g_32 = (safe_mod_func_int8_t_s_s((safe_lshift_func_uint8_t_u_s((l_31 &= ((l_30 = (2L || g_14)) & l_4)), 5)), 0x74L));
            for (l_30 = (-3); (l_30 <= 24); l_30 = safe_add_func_uint16_t_u_u(l_30, 6))
            { 
                uint16_t l_43 = 5UL;
                int32_t l_44 = 0x6E56995EL;
                l_44 = (((((safe_lshift_func_uint8_t_u_s((safe_sub_func_int32_t_s_s((((((safe_sub_func_uint8_t_u_u((l_9 = ((safe_mod_func_uint64_t_u_u((((((0x80D4L & g_32) == 0UL) | l_43) != 0x0B5CL) > l_43), g_14)) != 1L)), l_30)) != g_24) == 0x41L) == g_32) <= g_2), l_25)), 4)) | g_24) >= g_24) == g_32) && 0x51ECDE474C77A5C6LL);
                return g_24;
            }
        }
    }
    else
    { 
        uint16_t l_45 = 65535UL;
        l_9 = g_2;
        l_45 = 0xBCC772A3L;
        g_46 = g_3;
        g_48 = (g_47 |= ((g_24 = ((g_46 | 0xBC551464E9414028LL) | g_46)) <= l_4));
    }
    return g_48;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    transparent_crc(g_32, "g_32", print_hash_value);
    transparent_crc(g_46, "g_46", print_hash_value);
    transparent_crc(g_47, "g_47", print_hash_value);
    transparent_crc(g_48, "g_48", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
