// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1140.c
#include "csmith.h"


static long __undefined;



static int16_t g_3 = 0x51ADL;
static int16_t g_4 = 0xD53BL;
static int8_t g_5 = (-1L);
static int32_t g_6 = 0xEC541651L;
static uint32_t g_9 = 0x941FC9A5L;
static uint16_t g_12 = 65535UL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    int32_t l_2 = 0xAE9714A0L;
    int32_t l_7 = (-10L);
    int32_t l_8 = 0x276B87D0L;
    uint64_t l_18 = 1UL;
    if (l_2)
    { 
        return g_3;
    }
    else
    { 
        uint64_t l_15 = 0xECE3051EBF0DDD9CLL;
        ++g_9;
        l_8 ^= (-1L);
        --g_12;
        ++l_15;
    }
    l_18 = g_3;
    return g_3;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
