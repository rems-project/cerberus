// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1072.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x25B9B55BL;
static uint64_t g_9 = 0xE81A7ECC2443AC46LL;
static uint16_t g_13 = 0xE4B0L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint16_t l_5 = 0xBE18L;
    uint64_t l_6 = 18446744073709551615UL;
    int32_t l_12 = 0xB534DE6FL;
    for (g_2 = (-24); (g_2 < (-22)); g_2 = safe_add_func_int32_t_s_s(g_2, 5))
    { 
        return g_2;
    }
    l_12 = ((l_6 &= l_5) ^ (((safe_lshift_func_int8_t_s_s((g_9 ^= g_2), 5)) | ((safe_rshift_func_int16_t_s_u((1UL | l_5), g_2)) , g_2)) > l_5));
    g_13 ^= (g_2 || g_9);
    return g_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
