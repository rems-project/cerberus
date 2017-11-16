// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_414.c
#include "csmith.h"


static long __undefined;



static const int32_t g_2 = 0xB0F73838L;
static uint32_t g_6 = 4294967295UL;
static int32_t g_7 = 0xCAFE8B0DL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_3 = 0x64A53AA9AC70C309LL;
    int32_t l_4 = 0x5D811F07L;
    uint32_t l_5 = 0xDEDB5CABL;
    l_3 = g_2;
    l_4 = l_3;
    g_6 = l_5;
    g_7 = g_2;
    return l_5;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
