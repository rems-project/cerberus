// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1084.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = 0x0890L;
static int64_t g_8 = 0L;



static int8_t  func_1(void);
static int32_t  func_4(int16_t  p_5, int8_t  p_6);




static int8_t  func_1(void)
{ 
    uint32_t l_3 = 0xA654FDDDL;
    int32_t l_9 = (-1L);
    g_2 = 1L;
    l_3 = 0xA3DF603FL;
    l_9 = func_4((safe_unary_minus_func_int64_t_s(l_3)), g_2);
    return l_3;
}



static int32_t  func_4(int16_t  p_5, int8_t  p_6)
{ 
    g_8 |= 0x2C25FCC5L;
    return p_5;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
