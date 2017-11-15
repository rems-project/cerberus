// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_677.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x25B9B55BL;
static uint32_t g_5 = 0x18795010L;
static int64_t g_12 = (-1L);
static uint8_t g_13 = 0x2BL;
static uint8_t g_21 = 0x8EL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint64_t l_8 = 7UL;
    int32_t l_9 = 0x3AC46DDCL;
    int32_t l_10 = (-10L);
    int8_t l_11 = 0xA2L;
    for (g_2 = 12; (g_2 < (-10)); --g_2)
    { 
        uint8_t l_6 = 255UL;
        int32_t l_7 = 0xD6C3F0BCL;
        g_5 |= 0x20002526L;
        l_7 = l_6;
        l_7 &= l_8;
        ++g_13;
    }
    if (l_10)
    { 
        uint8_t l_16 = 0xF8L;
        int32_t l_17 = 0x53F3AC9DL;
        g_2 = 3L;
        l_17 = l_16;
        g_2 = g_13;
    }
    else
    { 
        int16_t l_18 = 0x2C5DL;
        int32_t l_19 = 0xE45D764CL;
        l_19 = l_18;
        g_2 = l_11;
        l_19 = g_2;
        g_2 ^= 0x3D0E72EEL;
    }
    if (l_10)
    { 
        uint16_t l_20 = 7UL;
        l_20 = g_5;
        l_10 = l_11;
    }
    else
    { 
        g_21++;
    }
    return l_10;
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
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
