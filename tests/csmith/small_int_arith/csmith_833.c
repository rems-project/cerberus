// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_833.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2 = 0xA1F94964A53AA9ACLL;
static uint16_t g_5 = 65534UL;
static int16_t g_9 = 0xEDB5L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_11 = 0xFE8B0D19L;
    int32_t l_12 = 0x6A927213L;
    g_2 = 0x28C176B0L;
    for (g_2 = 0; (g_2 >= 17); g_2 = safe_add_func_int8_t_s_s(g_2, 7))
    { 
        uint8_t l_8 = 0xB3L;
        int8_t l_10 = 0x44L;
        --g_5;
        g_9 &= l_8;
        if (l_10)
            break;
    }
    l_12 = l_11;
    return l_12;
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
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
