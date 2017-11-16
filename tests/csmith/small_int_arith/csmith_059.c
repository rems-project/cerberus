// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_059.c
#include "csmith.h"


static long __undefined;



static uint16_t g_3 = 0x58BAL;
static int32_t g_4 = 0xF737A9A9L;
static int16_t g_6 = 0x6AB2L;
static int32_t g_7 = 0x864BA8B3L;
static uint64_t g_13 = 0x9ADB821342F3D479LL;
static int32_t g_26 = 0x511ECBFCL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_2 = (-8L);
    int32_t l_8 = (-1L);
    int32_t l_9 = 0L;
    int32_t l_10 = 0x78213AF7L;
    int32_t l_11 = 5L;
    int32_t l_12 = 4L;
    g_4 = (((l_2 == g_3) <= 0xEE7D214C405B4019LL) > g_3);
    l_2 = ((((!g_3) ^ 255UL) > g_3) , g_4);
    g_13++;
    g_7 = ((safe_lshift_func_uint8_t_u_s((safe_mod_func_uint16_t_u_u(((safe_lshift_func_uint8_t_u_s((safe_sub_func_uint64_t_u_u((((((g_13++) > g_6) <= l_9) <= 0x67B38EB1L) != 0L), l_2)), l_10)) > 3UL), l_11)), 6)) , 0xFA5D8720L);
    return g_26;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
