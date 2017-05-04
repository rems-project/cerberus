// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_224.c
#include "csmith.h"


static long __undefined;



static int64_t g_4 = (-5L);
static uint32_t g_7 = 0x4BF8F0AAL;
static int8_t g_12 = 0xEFL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint16_t l_5 = 65534UL;
    int32_t l_6 = 0x66F5A9C4L;
    int32_t l_21 = (-9L);
    int32_t l_22 = 0x66EF3B06L;
    g_7 = ((l_6 = (safe_rshift_func_int8_t_s_u(g_4, l_5))) , l_5);
    l_6 = g_7;
    g_12 = (l_6 = (((safe_mod_func_int32_t_s_s((((safe_mod_func_int32_t_s_s(((g_4 , l_5) , g_4), 4294967295UL)) == 0x3A26L) ^ l_5), 0x56810853L)) , l_5) <= g_4));
    l_22 |= ((safe_sub_func_uint16_t_u_u((safe_lshift_func_int16_t_s_u((safe_mod_func_uint32_t_u_u((safe_lshift_func_uint16_t_u_u((1L & 4294967295UL), l_6)), (-1L))), l_5)), l_21)) && 0x0866L);
    return l_21;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
