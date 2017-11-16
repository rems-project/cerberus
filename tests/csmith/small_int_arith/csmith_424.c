// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_424.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x596960F5L;
static uint8_t g_6 = 0x6AL;
static uint64_t g_9 = 0x5A97963BA20B95AELL;
static int16_t g_12 = 0xEB4CL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int64_t l_13 = 0x14AD38DC5336DE01LL;
    g_2 ^= 0x60477862L;
    for (g_2 = 9; (g_2 < (-26)); g_2 = safe_sub_func_uint16_t_u_u(g_2, 9))
    { 
        uint16_t l_5 = 0x8974L;
        int32_t l_7 = 0xA924C000L;
        int32_t l_8 = 6L;
        g_6 |= l_5;
        g_9++;
        g_12 = g_9;
    }
    return l_13;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
