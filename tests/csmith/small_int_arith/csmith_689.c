// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_689.c
#include "csmith.h"


static long __undefined;



static uint32_t g_2 = 0xF46DB505L;
static int16_t g_7 = 9L;
static int32_t g_9 = 0xCBA86BA4L;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint8_t l_3 = 246UL;
    int32_t l_4 = 1L;
    g_2 = 0xD5E48D32L;
    l_4 = l_3;
    for (l_4 = (-19); (l_4 >= 6); l_4 = safe_add_func_uint32_t_u_u(l_4, 6))
    { 
        int8_t l_8 = 0L;
        g_7 = g_2;
        return l_8;
    }
    g_9 = g_2;
    return l_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
