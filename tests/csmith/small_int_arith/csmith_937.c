// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_937.c
#include "csmith.h"


static long __undefined;



static int32_t g_4 = 1L;
static uint64_t g_9 = 0UL;
static int64_t g_13 = 0xB0B4EF66B17B722BLL;
static uint64_t g_14 = 18446744073709551615UL;
static int16_t g_22 = 0L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint8_t l_5 = 0UL;
    const int32_t l_6 = 0x26FF23B1L;
    const int8_t l_7 = (-1L);
    uint16_t l_23 = 0xDCDAL;
    int8_t l_24 = 0x7DL;
    g_4 = ((safe_add_func_uint16_t_u_u((((l_5 ^= g_4) > l_6) >= g_4), g_4)) && l_5);
    if (((l_6 ^ l_7) > l_7))
    { 
        int16_t l_8 = 0x7084L;
        int32_t l_12 = 0xCB8F6C21L;
        --g_9;
        g_14++;
    }
    else
    { 
        uint8_t l_21 = 247UL;
        g_4 ^= (safe_div_func_uint8_t_u_u((g_22 = (safe_add_func_uint16_t_u_u((l_21 || g_14), 0x129BL))), l_23));
        return l_21;
    }
    return l_24;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
