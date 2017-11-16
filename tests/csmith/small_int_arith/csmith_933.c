// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_933.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = (-1L);
static uint16_t g_4 = 0x7723L;
static int32_t g_10 = 0xF4F88039L;
static int16_t g_18 = (-1L);
static uint32_t g_20 = 0xC86695CDL;
static uint64_t g_25 = 4UL;
static uint32_t g_33 = 0x2783DE76L;



static int32_t  func_1(void);
static int32_t  func_11(int64_t  p_12, int16_t  p_13, uint32_t  p_14);




static int32_t  func_1(void)
{ 
    int64_t l_3 = 0x66FE7D8A87013DCELL;
    uint32_t l_9 = 0x1D594D03L;
    int32_t l_38 = 0x5D3E8EA4L;
    g_4--;
    g_10 = (safe_mul_func_int8_t_s_s(((((((g_2 && 0xB568BE135E1F6F08LL) ^ 0x7059141AL) < g_2) ^ 0x4561L) & l_9) || 2L), l_9));
    if (g_10)
    { 
        return g_2;
    }
    else
    { 
        int8_t l_15 = 0xC8L;
        l_38 = func_11((0L <= 65534UL), g_2, l_15);
        l_38 = (+0x259CL);
    }
    return g_10;
}



static int32_t  func_11(int64_t  p_12, int16_t  p_13, uint32_t  p_14)
{ 
    int32_t l_19 = 0x19C44D4EL;
    int32_t l_29 = 0x891F433CL;
    uint16_t l_30 = 0UL;
    for (g_4 = 0; (g_4 <= 28); g_4 = safe_add_func_uint8_t_u_u(g_4, 7))
    { 
        uint16_t l_24 = 0x489BL;
        int32_t l_28 = 0x73E70D28L;
        g_20 ^= ((g_18 = 0x75L) ^ l_19);
        l_24 ^= ((safe_unary_minus_func_uint8_t_u((safe_lshift_func_uint8_t_u_u(((p_14 != (-7L)) ^ g_18), g_10)))) ^ l_19);
        ++g_25;
        ++l_30;
    }
    g_33++;
    for (g_33 = 0; (g_33 > 47); ++g_33)
    { 
        return g_20;
    }
    return l_29;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    transparent_crc(g_33, "g_33", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
