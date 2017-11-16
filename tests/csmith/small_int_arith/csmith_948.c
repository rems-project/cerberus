// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_948.c
#include "csmith.h"


static long __undefined;



static int32_t g_4 = (-1L);
static int8_t g_6 = 1L;
static int64_t g_8 = 0xFE57F6CC9CA3191BLL;
static uint32_t g_13 = 18446744073709551607UL;
static int32_t g_19 = 1L;
static uint64_t g_21 = 0xAEACB2D505BC9807LL;



static int32_t  func_1(void);
static int32_t  func_9(uint32_t  p_10);




static int32_t  func_1(void)
{ 
    int16_t l_2 = 0xCB50L;
    int32_t l_3 = 0xDD688769L;
    uint16_t l_20 = 0x3B88L;
    if ((l_3 |= ((l_2 < 4L) , l_2)))
    { 
        uint32_t l_5 = 7UL;
        g_6 = (((l_2 & 0L) == g_4) < l_5);
    }
    else
    { 
        int64_t l_7 = 0L;
        l_3 &= ((1L || 0x3D188047D2038E85LL) != l_7);
        g_8 = l_3;
        l_3 = func_9(l_7);
    }
    g_21 = (safe_mul_func_uint8_t_u_u((safe_mul_func_uint16_t_u_u((((((g_19 = l_3) == l_20) & g_4) , l_3) & 0xD0L), g_4)), (-1L)));
    return l_2;
}



static int32_t  func_9(uint32_t  p_10)
{ 
    int64_t l_11 = 1L;
    int32_t l_12 = 0x283D1F0DL;
    l_11 |= p_10;
lbl_14:
    l_12 = (0x157736D0C11E043ELL || 18446744073709551610UL);
    g_13 = ((1L != 0x54E5878EL) > 0xC3B7L);
    if (p_10)
        goto lbl_14;
    return g_8;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
