// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_610.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 0xDA4D073FL;
static int32_t g_10 = 0x17059141L;
static uint32_t g_13 = 0x9C2D621EL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int64_t l_2 = 0xF825E7A66FE7D8A8LL;
    uint64_t l_6 = 0x9951EA66E58D020BLL;
    int32_t l_11 = 0x9161D594L;
    int32_t l_12 = 0L;
    uint8_t l_16 = 0x94L;
    if (l_2)
    { 
        int16_t l_3 = (-3L);
        int32_t l_5 = 1L;
        g_4 = l_3;
        ++l_6;
        return g_4;
    }
    else
    { 
        int16_t l_9 = 0x8BE1L;
        l_9 = l_2;
        g_10 &= g_4;
        l_11 = (-2L);
    }
    l_11 = 0x7EA0D018L;
    g_13++;
    return l_16;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
