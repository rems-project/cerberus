// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_433.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xB13ECA4FL;
static int16_t g_3 = 0L;
static uint32_t g_8 = 0x7A61EEFBL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint64_t l_4 = 0x68876942A1E94870LL;
    int32_t l_10 = 0x4F4E7975L;
    g_3 = g_2;
    l_4 = 0xA0E60F95L;
    for (g_2 = (-8); (g_2 > 21); g_2 = safe_add_func_uint16_t_u_u(g_2, 1))
    { 
        uint64_t l_7 = 1UL;
        int32_t l_9 = 0x63D18804L;
        l_7 = g_2;
        g_8 = l_7;
        l_9 = g_8;
    }
    l_10 = 0x51AF7F3EL;
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
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
