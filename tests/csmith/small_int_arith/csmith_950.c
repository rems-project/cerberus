// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_950.c
#include "csmith.h"


static long __undefined;



static uint32_t g_7 = 0x6158D32FL;
static uint16_t g_9 = 0xFA2FL;
static uint32_t g_13 = 4UL;
static uint8_t g_16 = 0xC6L;



static int64_t  func_1(void);
static uint16_t  func_3(int32_t  p_4, int32_t  p_5, int64_t  p_6);




static int64_t  func_1(void)
{ 
    int8_t l_8 = (-1L);
    int32_t l_17 = 0xE40C18ABL;
    g_13 |= ((+func_3(g_7, l_8, l_8)) , g_9);
    g_16 = (safe_div_func_uint16_t_u_u((((0x8905B8B7L && g_13) || l_8) , g_9), l_8));
    l_17 |= g_9;
    return g_13;
}



static uint16_t  func_3(int32_t  p_4, int32_t  p_5, int64_t  p_6)
{ 
    int32_t l_12 = 0xF8C7B5C6L;
    g_9 = p_5;
    if ((safe_div_func_int32_t_s_s(((l_12 , 0xDE03L) || p_5), l_12)))
    { 
        return p_4;
    }
    else
    { 
        return p_4;
    }
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
