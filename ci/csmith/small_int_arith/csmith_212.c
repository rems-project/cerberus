// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_212.c
#include "csmith.h"


static long __undefined;



static uint32_t g_7 = 0x0F1D8987L;
static int32_t g_8 = (-1L);
static int32_t g_10 = 0x94B2AB76L;
static int32_t g_11 = 0x644ACCB2L;
static int8_t g_12 = (-8L);
static int8_t g_13 = 1L;
static int8_t g_14 = 3L;
static uint8_t g_18 = 0x52L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int32_t l_4 = 0xECBA2AFEL;
    int32_t l_9 = (-1L);
    int32_t l_15 = (-1L);
    int32_t l_16 = 1L;
    int32_t l_17 = 0xDBC56E70L;
    l_4 = (safe_lshift_func_uint16_t_u_s(0xA4A9L, 13));
    l_4 = (safe_rshift_func_uint16_t_u_u(g_7, 2));
    g_18--;
    return l_9;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
