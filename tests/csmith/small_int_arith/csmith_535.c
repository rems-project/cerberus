// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_535.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 0x3B6182EAL;
static int8_t g_6 = 1L;
static uint16_t g_10 = 0xDAFBL;



static const uint16_t  func_1(void);




static const uint16_t  func_1(void)
{ 
    uint64_t l_2 = 0xB90DA115252CB136LL;
    int32_t l_13 = 0L;
    if (l_2)
    { 
        uint16_t l_4 = 8UL;
        int64_t l_5 = (-2L);
        l_4 = g_3;
        g_6 = l_5;
        return l_5;
    }
    else
    { 
        uint32_t l_7 = 0x76EC7516L;
        l_7--;
        g_10--;
        l_13 = g_10;
    }
    l_13 |= 0xF29ACD40L;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
