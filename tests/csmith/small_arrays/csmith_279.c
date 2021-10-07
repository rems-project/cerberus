// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_279.c
#include "csmith.h"


static long __undefined;



static int64_t g_6 = 1L;
static int32_t g_15 = 4L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    int32_t l_10[3];
    int i;
    for (i = 0; i < 3; i++)
        l_10[i] = 0xE9646B8DL;
    if ((safe_rshift_func_int8_t_s_s((safe_sub_func_uint32_t_u_u(g_6, 3L)), 2)))
    { 
        uint8_t l_9 = 1UL;
        int8_t l_11 = 0xDDL;
        l_11 ^= ((((safe_div_func_uint8_t_u_u((l_9 > (l_9 == ((l_9 && g_6) >= 1L))), l_9)) || l_10[2]) ^ 0x55145CCBL) ^ l_9);
        return l_11;
    }
    else
    { 
        uint16_t l_12 = 0UL;
        --l_12;
        return g_15;
    }
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
