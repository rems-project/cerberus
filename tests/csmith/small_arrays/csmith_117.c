// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_117.c
#include "csmith.h"


static long __undefined;



static int32_t g_2[3] = {9L,9L,9L};
static uint32_t g_5 = 0x914D2EDCL;
static uint32_t g_11 = 4UL;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_12 = 18446744073709551608UL;
    for (g_2[2] = 0; (g_2[2] < 7); g_2[2] = safe_add_func_uint8_t_u_u(g_2[2], 7))
    { 
        int8_t l_10 = 0xE4L;
        g_5 = g_2[2];
        g_11 ^= (safe_add_func_uint16_t_u_u((((safe_mul_func_int8_t_s_s(0x74L, (((g_2[2] | l_10) , l_10) & 0x34B64B5CL))) && g_2[0]) != 0xB0L), (-7L)));
    }
    return l_12;
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    for (i = 0; i < 3; i++)
    {
        transparent_crc(g_2[i], "g_2[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
