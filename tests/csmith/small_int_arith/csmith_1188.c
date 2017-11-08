// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1188.c
#include "csmith.h"


static long __undefined;



static uint8_t g_5 = 1UL;
static uint16_t g_7 = 0xEDBDL;
static int64_t g_8 = 0x8D3A18E418A52733LL;
static uint16_t g_9 = 0x14B5L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint8_t l_2 = 0x4BL;
    const int8_t l_3 = 0x90L;
    int32_t l_4 = 0xDB8FAAAEL;
    int32_t l_6 = 0L;
    g_7 = (l_6 = ((l_4 = (l_2 & l_3)) <= (g_5 ^= (l_3 , l_3))));
    g_9--;
    return l_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
