// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1052.c
#include "csmith.h"


static long __undefined;



static uint64_t g_11 = 0xED9A924C00011151LL;
static int16_t g_16 = 0xB4C8L;
static uint32_t g_31 = 0x9F3B06D9L;
static uint64_t g_32 = 0x45487972E7EB6652LL;
static int16_t g_33 = (-7L);



static uint16_t  func_1(void);
static int32_t  func_2(uint32_t  p_3, uint8_t  p_4, int32_t  p_5, int32_t  p_6);
static int64_t  func_20(uint32_t  p_21, int32_t  p_22, uint32_t  p_23, int64_t  p_24, int8_t  p_25);




static uint16_t  func_1(void)
{ 
    int16_t l_10 = 0x756AL;
    int32_t l_17 = 8L;
    g_33 = func_2((safe_lshift_func_uint8_t_u_u(((g_11 = (!l_10)) <= (l_17 = (safe_rshift_func_int16_t_s_u(((safe_mul_func_uint16_t_u_u(65526UL, l_10)) ^ g_16), g_16)))), g_16)), g_16, l_10, g_16);
    return l_17;
}



static int32_t  func_2(uint32_t  p_3, uint8_t  p_4, int32_t  p_5, int32_t  p_6)
{ 
    int32_t l_28 = 0xFBFC75DAL;
    g_32 |= (p_5 && (g_31 &= ((safe_lshift_func_uint8_t_u_u(((((0xF5AC3D6C1DFE936BLL ^ func_20(((safe_rshift_func_int16_t_s_s(p_3, 15)) ^ 0L), g_11, l_28, g_16, p_4)) > l_28) > g_16) && g_16), 1)) , 0xC7L)));
    return l_28;
}



static int64_t  func_20(uint32_t  p_21, int32_t  p_22, uint32_t  p_23, int64_t  p_24, int8_t  p_25)
{ 
    uint32_t l_29 = 0xE3D97867L;
    uint64_t l_30 = 0x6B5CFDA6C2E3A4C6LL;
    l_29 = 0L;
    return l_30;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    transparent_crc(g_32, "g_32", print_hash_value);
    transparent_crc(g_33, "g_33", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
