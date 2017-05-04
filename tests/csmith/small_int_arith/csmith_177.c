// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_177.c
#include "csmith.h"


static long __undefined;



static int8_t g_7 = 0x8FL;
static int8_t g_9 = 0xABL;
static int8_t g_19 = 3L;
static uint64_t g_21 = 18446744073709551612UL;
static uint32_t g_24 = 4294967295UL;
static uint32_t g_28 = 1UL;
static int32_t g_29 = 0L;
static uint32_t g_30 = 4294967295UL;
static int8_t g_39 = 0xF8L;
static int64_t g_44 = 0x7C242EA6AE202455LL;
static int16_t g_48 = 0x61FAL;
static int32_t g_50 = 0x3B72B46FL;
static int16_t g_51 = 0x7974L;
static int16_t g_53 = (-2L);
static int16_t g_55 = (-1L);
static uint16_t g_56 = 4UL;
static int32_t g_59 = 4L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint16_t l_5 = 1UL;
    int32_t l_6 = 1L;
    int32_t l_8 = 0x07D7C118L;
    int32_t l_20 = 0x21046671L;
    int32_t l_52 = 0xE68266C0L;
    if (((safe_div_func_uint8_t_u_u((l_8 = (((~((((l_6 = l_5) , l_6) , g_7) || g_7)) > l_5) , 9UL)), 1UL)) , g_7))
    { 
        g_9 = ((g_7 == g_7) , g_7);
        if (l_5)
            goto lbl_27;
    }
    else
    { 
        uint32_t l_12 = 4294967292UL;
        int32_t l_18 = 1L;
        for (l_6 = 14; (l_6 >= (-8)); l_6--)
        { 
            uint32_t l_13 = 0UL;
            l_13 = l_12;
            l_18 ^= (safe_rshift_func_uint8_t_u_s(((safe_mul_func_int16_t_s_s((-1L), g_9)) & 1L), g_9));
            if (g_7)
                goto lbl_27;
        }
        g_21++;
        if (l_5)
            goto lbl_27;
    }
lbl_27:
    g_24++;
    if ((g_28 && (-2L)))
    { 
        int32_t l_33 = (-8L);
        int8_t l_34 = (-2L);
        int32_t l_35 = (-1L);
        g_30--;
        l_34 = (l_33 = 0xDFD99643L);
        l_35 ^= (l_33 ^ l_33);
    }
    else
    { 
        uint32_t l_38 = 0xB3915004L;
        int32_t l_45 = 0x98564DBBL;
        int32_t l_46 = 0L;
        int32_t l_47 = 0xC8A2DB63L;
        for (g_28 = 19; (g_28 <= 10); --g_28)
        { 
            int32_t l_49 = 0xF903A798L;
            int32_t l_54 = 5L;
            g_39 = (l_6 |= l_38);
            g_44 |= (((safe_rshift_func_uint16_t_u_u(g_30, g_30)) < 0UL) , l_20);
            g_56++;
        }
        l_46 = (l_47 = g_24);
    }
    g_59 = l_52;
    return l_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    transparent_crc(g_29, "g_29", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    transparent_crc(g_39, "g_39", print_hash_value);
    transparent_crc(g_44, "g_44", print_hash_value);
    transparent_crc(g_48, "g_48", print_hash_value);
    transparent_crc(g_50, "g_50", print_hash_value);
    transparent_crc(g_51, "g_51", print_hash_value);
    transparent_crc(g_53, "g_53", print_hash_value);
    transparent_crc(g_55, "g_55", print_hash_value);
    transparent_crc(g_56, "g_56", print_hash_value);
    transparent_crc(g_59, "g_59", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
