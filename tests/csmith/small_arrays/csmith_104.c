// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_104.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 65535UL;
static int8_t g_4 = 2L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint16_t l_6 = 3UL;
    int32_t l_22 = (-6L);
    int32_t l_23 = 1L;
    if (g_2)
    { 
        return g_2;
    }
    else
    { 
        int64_t l_3 = 0x8ECF54C3C69AED23LL;
        int32_t l_5[4] = {4L,4L,4L,4L};
        int32_t l_18 = 0xF985589BL;
        int32_t l_19[4] = {0x89BDD777L,0x89BDD777L,0x89BDD777L,0x89BDD777L};
        int i;
        --l_6;
        l_5[1] = (g_4 || (l_19[2] &= (safe_mod_func_uint16_t_u_u((l_18 ^= (safe_rshift_func_int16_t_s_s((+(safe_sub_func_int32_t_s_s(((g_4 , (safe_sub_func_int16_t_s_s(0x4CB8L, l_5[0]))) , 1L), g_4))), l_5[2]))), g_2))));
        l_18 &= (safe_mul_func_int8_t_s_s((l_23 |= (l_22 = 0x9AL)), l_19[1]));
        return g_4;
    }
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
