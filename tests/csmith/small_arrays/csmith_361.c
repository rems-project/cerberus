// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_361.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2[4] = {0x720EL,0x720EL,0x720EL,0x720EL};
static uint64_t g_13 = 0xCC099A56718E5034LL;



static uint64_t  func_1(void);
static int32_t  func_3(int32_t  p_4);




static uint64_t  func_1(void)
{ 
    int16_t l_16 = 1L;
    g_2[3] = 8L;
    l_16 |= func_3(g_2[2]);
    return l_16;
}



static int32_t  func_3(int32_t  p_4)
{ 
    int32_t l_12 = 0xEE4C20F7L;
    int32_t l_15 = 0x5DA2A0C0L;
    for (p_4 = (-17); (p_4 <= 23); p_4 = safe_add_func_uint64_t_u_u(p_4, 7))
    { 
        uint8_t l_7[3];
        int32_t l_14[4];
        int i;
        for (i = 0; i < 3; i++)
            l_7[i] = 0xA8L;
        for (i = 0; i < 4; i++)
            l_14[i] = 0x6C715341L;
        l_15 = (l_14[0] = ((l_7[2] , ((p_4 | ((((((((safe_sub_func_uint8_t_u_u((safe_lshift_func_uint8_t_u_s((g_2[1] >= p_4), 3)), 0xDBL)) != g_2[3]) < 0xB3A00D0E75D5F8D9LL) != l_12) & g_13) , g_13) == p_4) == p_4)) | 1UL)) || 4294967286UL));
    }
    return g_13;
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    for (i = 0; i < 4; i++)
    {
        transparent_crc(g_2[i], "g_2[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
