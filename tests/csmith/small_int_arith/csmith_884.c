// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_884.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x8A61928CL;
static uint8_t g_6 = 0x82L;
static uint32_t g_8 = 0x938DD44AL;
static uint32_t g_9 = 0xECAFE8B0L;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int8_t l_5 = 0xC3L;
    int32_t l_14 = 0xF93BD5DEL;
    uint64_t l_15 = 1UL;
    for (g_2 = 17; (g_2 >= (-16)); g_2 = safe_sub_func_int16_t_s_s(g_2, 3))
    { 
        uint32_t l_7 = 0x11F07B4BL;
        g_6 |= l_5;
        l_7 = g_2;
        g_8 = 0xB3B7BEDEL;
        g_9--;
    }
    g_2 = 0L;
    g_2 = g_9;
    if (g_8)
    { 
        uint32_t l_12 = 18446744073709551611UL;
        int32_t l_13 = 0x6BC657E3L;
        g_2 |= g_8;
        l_12 = g_8;
        l_13 = l_5;
        l_14 = l_5;
    }
    else
    { 
        ++l_15;
        g_2 |= g_8;
    }
    return g_9;
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
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
