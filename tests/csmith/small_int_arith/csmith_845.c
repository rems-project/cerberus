// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_845.c
#include "csmith.h"


static long __undefined;



static int8_t g_7 = 0x21L;
static uint8_t g_9 = 255UL;
static uint32_t g_12 = 0xF6B3E713L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint16_t l_2 = 0x971CL;
    int32_t l_5 = 0x0CD50997L;
    int16_t l_8 = 0x70A3L;
    int32_t l_15 = (-4L);
    int8_t l_16 = 0x7FL;
    l_2 ^= 6L;
    for (l_2 = 26; (l_2 >= 43); l_2 = safe_add_func_uint8_t_u_u(l_2, 8))
    { 
        uint64_t l_6 = 0xB98764276038591BLL;
        l_5 &= 0xC0AA39EDL;
        l_5 = 0x3B3F3656L;
        g_7 = l_6;
        l_8 ^= (-1L);
    }
    if (g_7)
    { 
        g_9--;
        g_12 = 7L;
        l_5 ^= g_7;
    }
    else
    { 
        uint32_t l_13 = 0x4EDF0EBFL;
        int32_t l_14 = 0xD8AF8716L;
        l_14 = l_13;
        l_14 = 1L;
    }
    l_15 = 0x51EF9953L;
    return l_16;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
