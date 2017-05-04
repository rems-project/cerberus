// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_346.c
#include "csmith.h"


static long __undefined;



static uint64_t g_7 = 0xBEDEDB5CABFC3938LL;
static int32_t g_8 = 0x74006310L;
static int64_t g_15 = 4L;
static uint16_t g_19 = 65528UL;
static uint64_t g_20 = 1UL;
static int16_t g_23 = 4L;
static uint32_t g_24 = 0x7C422D5FL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_6 = 5UL;
    int32_t l_21 = 5L;
    int16_t l_31 = 1L;
    int8_t l_32 = 0xB3L;
    int8_t l_33 = 3L;
    g_8 = (g_7 = (safe_add_func_uint64_t_u_u(((safe_sub_func_int8_t_s_s(0xF9L, l_6)) , 18446744073709551612UL), 0x845D811F07B4BC66LL)));
lbl_27:
    for (g_8 = 0; (g_8 >= 24); g_8 = safe_add_func_uint32_t_u_u(g_8, 8))
    { 
        int32_t l_14 = 0x7921E124L;
        uint16_t l_18 = 65535UL;
        for (g_7 = (-12); (g_7 < 34); ++g_7)
        { 
            uint32_t l_22 = 0x6084EDC0L;
            g_15 = (+(l_14 <= l_6));
            l_21 = (g_20 = (safe_div_func_int16_t_s_s((g_19 = ((g_8 > l_18) , g_15)), 0x7627L)));
            if (l_22)
                continue;
            if (l_22)
                goto lbl_27;
            --g_24;
        }
    }
    l_32 &= ((safe_lshift_func_int8_t_s_s((safe_unary_minus_func_int16_t_s(l_21)), 4)) ^ l_31);
    g_8 &= (g_15 || l_6);
    return l_33;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
