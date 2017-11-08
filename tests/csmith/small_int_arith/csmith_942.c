// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_942.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 18446744073709551611UL;
static uint64_t g_13 = 0x8E418A52733582F8LL;



static int32_t  func_1(void);
static uint8_t  func_6(const int8_t  p_7, uint32_t  p_8);




static int32_t  func_1(void)
{ 
    uint32_t l_2 = 1UL;
    int64_t l_9 = 8L;
    int32_t l_14 = 0x977A1245L;
    int32_t l_15 = 0xA90611BCL;
    g_3 = l_2;
    l_15 = ((l_14 = (safe_sub_func_uint8_t_u_u(func_6(l_2, l_9), l_2))) < l_2);
    return g_3;
}



static uint8_t  func_6(const int8_t  p_7, uint32_t  p_8)
{ 
    int32_t l_12 = 8L;
    g_13 = (safe_div_func_uint64_t_u_u((g_3 | g_3), l_12));
    return p_7;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
