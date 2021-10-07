// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_181.c
#include "csmith.h"


static long __undefined;



static int32_t g_9 = 0x1449C9FBL;
static int16_t g_10[2] = {0x25FCL,0x25FCL};



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_6 = (-9L);
    int32_t l_11 = 0x91DF82D8L;
    g_10[0] &= (safe_mul_func_int64_t_s_s((safe_sub_func_int8_t_s_s(l_6, 0xDFL)), ((safe_mul_func_uint8_t_u_u((l_6 , l_6), g_9)) != l_6)));
    l_11 &= l_6;
    g_9 = ((l_6 , (safe_mul_func_int8_t_s_s((l_6 , (g_10[0] && 0x72D714F98CAFA32FLL)), 2L))) <= l_11);
    if ((l_11 = 7L))
    { 
        return g_9;
    }
    else
    { 
        uint8_t l_14 = 0x23L;
        int32_t l_17 = 1L;
        l_14++;
        l_17 |= l_6;
        return g_10[0];
    }
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_9, "g_9", print_hash_value);
    for (i = 0; i < 2; i++)
    {
        transparent_crc(g_10[i], "g_10[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
