// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1182.c
#include "csmith.h"


static long __undefined;



static int32_t g_8 = 0xEFC07E17L;
static int8_t g_10 = 0xCEL;



static uint32_t  func_1(void);
static int8_t  func_4(uint16_t  p_5, uint16_t  p_6, const uint16_t  p_7);




static uint32_t  func_1(void)
{ 
    uint16_t l_9 = 0x3FBBL;
    uint32_t l_11 = 1UL;
    l_11 = (safe_add_func_int64_t_s_s((g_10 ^= (func_4(g_8, l_9, g_8) , 0xCE3E63E31551DA62LL)), l_9));
    return l_9;
}



static int8_t  func_4(uint16_t  p_5, uint16_t  p_6, const uint16_t  p_7)
{ 
    return g_8;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
