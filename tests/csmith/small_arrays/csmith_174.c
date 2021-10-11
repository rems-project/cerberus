// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_174.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 0x251D69F4L;
static int16_t g_15[1] = {0x9958L};



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint16_t l_9 = 1UL;
    uint16_t l_10 = 0xD010L;
    int32_t l_11 = (-1L);
    uint32_t l_12 = 0x05732AA6L;
    uint32_t l_16 = 0xA3187110L;
    l_11 = ((safe_mod_func_int16_t_s_s(g_4, (((safe_mul_func_int16_t_s_s(g_4, ((safe_mul_func_int16_t_s_s((g_4 , l_9), 0L)) > 0x2250L))) >= g_4) , l_9))) != l_10);
    l_12++;
    g_15[0] = (-2L);
    l_11 = l_16;
    return g_15[0];
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_15[i], "g_15[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
