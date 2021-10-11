// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_272.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 0xDD1E1E87L;
static uint8_t g_13 = 0xF0L;
static uint32_t g_15 = 4294967293UL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int32_t l_2[3];
    uint32_t l_14 = 18446744073709551615UL;
    int32_t l_17 = 0x7BDD4840L;
    int i;
    for (i = 0; i < 3; i++)
        l_2[i] = 2L;
    for (g_3 = 2; (g_3 >= 0); g_3 -= 1)
    { 
        int16_t l_16[3];
        int i;
        for (i = 0; i < 3; i++)
            l_16[i] = 0xEE24L;
        l_17 &= (4UL & (((((safe_add_func_uint16_t_u_u(((((g_15 = ((safe_lshift_func_int8_t_s_s((g_13 = (safe_sub_func_uint32_t_u_u((+0L), ((safe_add_func_int8_t_s_s(g_3, l_2[2])) <= 65535UL)))), l_2[1])) , l_14)) != (-1L)) ^ l_14) | l_14), 0x1E2DL)) && 0L) & 0x4856CD83L) ^ 0xEC58F553L) , l_16[1]));
        return l_2[g_3];
    }
    l_17 = 0x0335900BL;
    return l_2[0];
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
    transparent_crc(g_15, "g_15", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
