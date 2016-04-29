// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_299.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 1L;
static uint32_t g_10 = 0x9EC4279CL;
static int32_t g_15 = 0xFBD3AEB5L;
static int32_t g_16 = (-1L);
static uint16_t g_28 = 0x1791L;
static int32_t g_33 = 0xB6CE1A81L;
static int16_t g_35 = 0L;
static uint32_t g_38 = 0x9E1A0E1CL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint64_t l_23 = 8UL;
    int32_t l_26 = (-1L);
    int32_t l_34 = 0xF1BB1300L;
    int32_t l_36 = (-1L);
    int32_t l_37 = 1L;
    for (g_2 = 0; (g_2 < (-20)); g_2 = safe_sub_func_uint8_t_u_u(g_2, 4))
    { 
        uint64_t l_5 = 0x837BC75286E871D9LL;
        ++l_5;
        g_10 = ((safe_mod_func_int8_t_s_s(g_2, 0x7EL)) == 0xB5L);
        g_16 = (g_15 = (safe_sub_func_uint8_t_u_u(((safe_sub_func_int8_t_s_s(g_10, l_5)) | g_10), g_2)));
    }
    for (g_2 = 2; (g_2 < 20); g_2 = safe_add_func_int64_t_s_s(g_2, 2))
    { 
        uint32_t l_25 = 0x5849968CL;
        int32_t l_27 = 0x6A0B5978L;
        for (g_16 = (-19); (g_16 == 0); g_16 = safe_add_func_int16_t_s_s(g_16, 7))
        { 
            for (g_15 = 0; (g_15 <= (-22)); g_15 = safe_sub_func_int16_t_s_s(g_15, 1))
            { 
                int32_t l_24 = (-1L);
                l_24 |= (g_16 && l_23);
            }
            g_15 = 0L;
            return g_10;
        }
        l_26 &= l_25;
        ++g_28;
        g_15 = ((safe_lshift_func_uint16_t_u_u((g_33 = ((0x1CL < g_16) & 0L)), 12)) >= g_28);
    }
    --g_38;
    g_2 = ((safe_lshift_func_int8_t_s_u(l_34, l_37)) ^ 3L);
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    transparent_crc(g_33, "g_33", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
