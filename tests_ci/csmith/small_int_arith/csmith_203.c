// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_203.c
#include "csmith.h"


static long __undefined;



static int16_t g_3 = 0x8E97L;
static int64_t g_19 = 0x108531D14CD49598LL;
static int64_t g_20 = 0x46B43D2717F4039ELL;
static uint8_t g_21 = 1UL;
static int64_t g_22 = 0xEF3B0639E6A4137DLL;
static int64_t g_23 = (-1L);



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int16_t l_2 = 0xB7C7L;
    int32_t l_4 = 0xB4074DD0L;
    l_4 ^= (l_2 < g_3);
    l_4 = (g_21 = (((safe_lshift_func_uint8_t_u_s((!((safe_sub_func_int16_t_s_s(((g_20 |= (((safe_mod_func_uint8_t_u_u(((safe_mul_func_uint16_t_u_u(((g_19 = (safe_lshift_func_uint8_t_u_u((!(safe_add_func_uint16_t_u_u(65535UL, 1UL))), 6))) >= 1L), 0x27FAL)) != l_2), (-1L))) && g_19) > g_3)) == 0x6B42BE197E7C14ABLL), g_3)) , 4294967295UL)), 4)) || g_19) ^ g_3));
    g_22 = l_4;
    g_23 = l_4;
    return l_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
