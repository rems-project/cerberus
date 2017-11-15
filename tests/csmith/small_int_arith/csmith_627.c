// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_627.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = 0x8DL;
static uint64_t g_3 = 0xF4F46DB5052061F6LL;
static int32_t g_6 = 0xEE7D214CL;
static int32_t g_7 = 0L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint32_t l_8 = 0x1867B8F5L;
    uint64_t l_11 = 0xA47C9D5FAC12265ELL;
    int32_t l_12 = 1L;
    --g_3;
    g_6 = g_2;
    if (g_6)
    { 
        g_7 = g_3;
        l_8--;
    }
    else
    { 
        return g_3;
    }
    l_12 = l_11;
    return g_7;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
