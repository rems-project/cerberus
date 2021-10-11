// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_162.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = 3L;
static int32_t g_9 = 0L;
static uint64_t g_20 = 0xAE4F78D7CBAE8B01LL;



static const uint8_t  func_1(void);
static int64_t  func_5(const int16_t  p_6, int8_t  p_7);




static const uint8_t  func_1(void)
{ 
    int16_t l_3[2];
    int32_t l_4[2];
    int i;
    for (i = 0; i < 2; i++)
        l_3[i] = (-10L);
    for (i = 0; i < 2; i++)
        l_4[i] = 8L;
    l_3[1] ^= g_2;
    l_4[1] = g_2;
    g_9 = (func_5(l_3[1], l_3[1]) == g_2);
    l_4[0] = (l_4[1] , (safe_div_func_int8_t_s_s(((safe_lshift_func_uint8_t_u_s(func_5(l_4[1], (g_2 , 0x74L)), 3)) < l_3[1]), g_2)));
    g_9 = ((safe_mul_func_uint8_t_u_u((safe_sub_func_int32_t_s_s(0x167C28CAL, (safe_mul_func_uint8_t_u_u((g_20 = (0x1C23L || g_2)), l_3[1])))), 0xA3L)) ^ g_2);
    return g_20;
}



static int64_t  func_5(const int16_t  p_6, int8_t  p_7)
{ 
    uint32_t l_8 = 0xC443EB60L;
    return l_8;
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
    transparent_crc(g_20, "g_20", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
