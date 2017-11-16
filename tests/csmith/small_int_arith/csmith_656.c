// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_656.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x477862FDL;
static uint32_t g_10 = 0x649F6D4AL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_5 = 0x67FA5C62L;
    int32_t l_6 = 0L;
    int32_t l_7 = 1L;
    int32_t l_8 = 5L;
    int32_t l_9 = 0L;
    for (g_2 = 23; (g_2 >= (-20)); g_2 = safe_sub_func_int64_t_s_s(g_2, 5))
    { 
        l_5 ^= 1L;
        return g_2;
    }
    g_2 = g_2;
    g_10--;
    return l_7;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
