// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_189.c
#include "csmith.h"


static long __undefined;



static int64_t g_7[2] = {(-9L),(-9L)};
static int32_t g_8 = (-4L);



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint64_t l_2 = 0x184C506D444182BDLL;
    uint32_t l_9[1];
    int i;
    for (i = 0; i < 1; i++)
        l_9[i] = 0x996F377CL;
    g_8 = (l_2 > ((safe_add_func_uint8_t_u_u(((safe_add_func_uint16_t_u_u((l_2 >= l_2), g_7[1])) ^ 0x36544D1878ABC106LL), 3L)) , l_2));
    return l_9[0];
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    for (i = 0; i < 2; i++)
    {
        transparent_crc(g_7[i], "g_7[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
