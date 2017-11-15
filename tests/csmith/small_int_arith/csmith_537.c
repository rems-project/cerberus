// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_537.c
#include "csmith.h"


static long __undefined;



static int16_t g_3 = 0L;
static uint64_t g_6 = 0x3921DED680444555LL;
static int32_t g_9 = (-1L);
static uint32_t g_12 = 18446744073709551615UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    const int32_t l_2 = 0x85299DADL;
    int32_t l_5 = 0x8FAAAEB9L;
    int32_t l_10 = 0L;
    int32_t l_11 = (-1L);
    if (l_2)
    { 
        int32_t l_4 = 0x5AB3E90AL;
        g_6--;
        g_9 = 0x4D9EDBDAL;
        --g_12;
    }
    else
    { 
        int32_t l_15 = 0x4A90611BL;
        l_15 = g_3;
        g_9 |= 0xEE39F3FAL;
        return g_12;
    }
    return l_11;
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
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
