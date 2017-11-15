// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_939.c
#include "csmith.h"


static long __undefined;



static uint64_t g_11 = 18446744073709551615UL;
static uint8_t g_17 = 255UL;
static int16_t g_20 = (-3L);
static int32_t g_24 = 0x53526C71L;
static int32_t g_25 = (-1L);
static int8_t g_26 = 0xA2L;
static uint16_t g_27 = 0x7525L;



static int32_t  func_1(void);
static int32_t  func_4(int32_t  p_5, uint8_t  p_6, uint8_t  p_7, int8_t  p_8, const int16_t  p_9);




static int32_t  func_1(void)
{ 
    int8_t l_2 = 9L;
    int32_t l_3 = 0xF37831E4L;
    int64_t l_10 = (-6L);
    l_3 |= (l_2 || l_2);
    l_3 = l_3;
    l_3 = func_4(l_10, l_2, g_11, g_11, g_11);
    g_24 &= l_3;
    return g_20;
}



static int32_t  func_4(int32_t  p_5, uint8_t  p_6, uint8_t  p_7, int8_t  p_8, const int16_t  p_9)
{ 
    int64_t l_15 = (-10L);
    int32_t l_21 = 0xA56718E5L;
    int32_t l_22 = (-7L);
    for (p_8 = 0; (p_8 >= (-13)); p_8 = safe_sub_func_uint32_t_u_u(p_8, 8))
    { 
        uint64_t l_14 = 0xA29F58382BDB979CLL;
        int32_t l_16 = 0L;
        int32_t l_23 = 0x52487223L;
        l_15 = (((g_11 <= p_8) || g_11) != l_14);
        ++g_17;
        ++g_27;
        l_23 = (p_6 , 0xB07FB07DL);
    }
    g_24 &= g_26;
    return l_22;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
