// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_304.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static uint32_t g_5 = 0x6951AD38L;
static int64_t g_11 = 3L;
static int16_t g_13 = 0x6CE4L;
static uint8_t g_15 = 1UL;
static int32_t g_18 = (-6L);
static int16_t g_19 = 0xDACDL;
static uint8_t g_22 = 0xCFL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint32_t l_9[3];
    int32_t l_10 = 0x6B87D0FAL;
    int32_t l_12 = 0x5047C4D1L;
    int32_t l_14 = 0x1D1B9849L;
    int32_t l_20 = 0xAFA01777L;
    int32_t l_21[2];
    int i;
    for (i = 0; i < 3; i++)
        l_9[i] = 0xA6DEEC54L;
    for (i = 0; i < 2; i++)
        l_21[i] = 0x61780EECL;
    for (g_2 = 18; (g_2 < (-12)); g_2 = safe_sub_func_int8_t_s_s(g_2, 1))
    { 
        uint32_t l_8 = 4294967286UL;
        g_5++;
        l_8 = (-2L);
        return l_9[2];
    }
    l_10 &= 4L;
    g_15++;
    ++g_22;
    return l_9[0];
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
