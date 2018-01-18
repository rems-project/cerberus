// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_613.c
#include "csmith.h"


static long __undefined;



static int16_t g_3 = 0x47DCL;
static int32_t g_4 = 0x265AB3E9L;
static int8_t g_7 = 0x68L;
static int32_t g_8 = (-5L);
static uint16_t g_14 = 0x7E4AL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int32_t l_2 = 0L;
    int32_t l_6 = (-7L);
    int32_t l_10 = 0x9E2A8D3AL;
    int32_t l_11 = 0xA5273358L;
    int32_t l_12 = (-5L);
    if (l_2)
    { 
        int32_t l_5 = 8L;
        int32_t l_9 = 0xD9EDBDA7L;
        int32_t l_13 = 0x0977A124L;
        g_4 = g_3;
        g_14++;
    }
    else
    { 
        return l_2;
    }
    if (g_4)
    { 
        uint16_t l_17 = 1UL;
        return l_17;
    }
    else
    { 
        int16_t l_18 = (-7L);
        l_18 = l_12;
        return l_18;
    }
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
