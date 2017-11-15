// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_634.c
#include "csmith.h"


static long __undefined;



static uint64_t g_3 = 1UL;
static uint8_t g_4 = 9UL;
static uint64_t g_8 = 0xF0AA6E6F7FBF2121LL;
static uint32_t g_9 = 0x20E32CF4L;
static int64_t g_10 = 1L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_2 = 0L;
    if (l_2)
    { 
        return g_3;
    }
    else
    { 
        uint32_t l_7 = 0xD3C891C5L;
        g_4--;
        g_8 = l_7;
    }
    g_9 = 0x88E17B84L;
    g_10 ^= (-9L);
    return g_10;
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
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
