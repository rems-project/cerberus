// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_393.c
#include "csmith.h"


static long __undefined;



static int32_t g_7 = (-1L);
static uint16_t g_8 = 9UL;
static uint64_t g_12 = 0x19F23E52509E71B3LL;
static int32_t g_17 = 1L;
static uint8_t g_18 = 0xDBL;
static uint32_t g_21 = 1UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint16_t l_6 = 0xA2A3L;
    int16_t l_9 = 0xE21AL;
    int32_t l_10 = 0xF1A969ACL;
    int32_t l_11 = 0xEE34EDF6L;
    int32_t l_15 = 0x50D8AF87L;
    int32_t l_16 = 3L;
    l_10 = ((((((((g_8 ^= (safe_sub_func_int16_t_s_s((safe_mod_func_uint8_t_u_u((l_6 <= g_7), g_7)), 0UL))) ^ g_7) , g_8) < l_9) && 0x4FDA7EF5L) == g_7) & g_7) == l_6);
    g_12++;
    g_18++;
    ++g_21;
    return l_16;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
