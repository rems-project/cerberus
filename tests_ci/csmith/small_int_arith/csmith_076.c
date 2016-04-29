// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_076.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-8L);
static int16_t g_7 = 0x5F49L;
static int16_t g_13 = 1L;
static uint32_t g_14 = 1UL;
static int64_t g_15 = 0L;
static int8_t g_18 = 1L;
static uint64_t g_22 = 0x166C1932E3CA3691LL;
static int8_t g_36 = 0xCDL;
static int32_t g_40 = (-1L);
static int8_t g_41 = 0x8CL;
static int8_t g_43 = 0xE0L;
static uint16_t g_45 = 1UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint8_t l_5 = 0xF7L;
    int32_t l_6 = (-2L);
    int32_t l_16 = (-1L);
    int32_t l_17 = (-1L);
    int32_t l_19 = 0x5F7919ADL;
    int32_t l_20 = (-1L);
    int32_t l_21 = 0x1CE3CB5AL;
    for (g_2 = 0; (g_2 >= (-5)); g_2 = safe_sub_func_int64_t_s_s(g_2, 1))
    { 
        int64_t l_12 = (-1L);
        g_7 = (l_6 = ((0xFC558BAC04EE7D21LL | 0x405B40194DDBC370LL) || l_5));
        g_13 &= (safe_add_func_int32_t_s_s((safe_lshift_func_int8_t_s_u(l_12, l_12)), 0x831EB239L));
        g_14 = 0x5A9864BAL;
        if (g_2)
            goto lbl_31;
        g_22++;
    }
lbl_31:
    l_6 = ((safe_sub_func_int64_t_s_s(((((safe_sub_func_int64_t_s_s((safe_mul_func_int16_t_s_s(g_13, 0UL)), g_22)) , 0L) ^ 0L) , l_6), g_13)) >= l_19);
    for (g_18 = 0; (g_18 >= 14); g_18 = safe_add_func_int32_t_s_s(g_18, 7))
    { 
        int32_t l_34 = (-6L);
        int32_t l_35 = 0xFCF419C2L;
        int32_t l_37 = (-5L);
        int32_t l_38 = 0x89405DBDL;
        int32_t l_39 = 0xD9AB8A87L;
        int32_t l_42 = (-1L);
        int32_t l_44 = 1L;
        uint16_t l_50 = 0x95C1L;
        g_45++;
        l_44 ^= (safe_mul_func_int8_t_s_s(((((0xE7A32987L < l_50) <= (-1L)) && l_17) ^ g_41), l_20));
    }
    g_2 = (255UL < 0x3EL);
    return g_15;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_36, "g_36", print_hash_value);
    transparent_crc(g_40, "g_40", print_hash_value);
    transparent_crc(g_41, "g_41", print_hash_value);
    transparent_crc(g_43, "g_43", print_hash_value);
    transparent_crc(g_45, "g_45", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
