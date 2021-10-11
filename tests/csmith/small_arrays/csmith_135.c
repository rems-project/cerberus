// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_135.c
#include "csmith.h"


static long __undefined;



static uint8_t g_8 = 254UL;
static uint16_t g_13 = 0x7A12L;
static uint32_t g_14[4] = {0x90611BC3L,0x90611BC3L,0x90611BC3L,0x90611BC3L};



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int32_t l_9 = 0xE77AB392L;
    if ((safe_div_func_uint32_t_u_u((safe_unary_minus_func_int16_t_s(((safe_add_func_int16_t_s_s(((~g_8) || l_9), l_9)) < g_8))), g_8)))
    { 
        int32_t l_12 = (-6L);
        g_13 = (l_9 >= ((safe_rshift_func_int16_t_s_s((0L <= l_12), 5)) , g_8));
        g_14[2]--;
        return l_12;
    }
    else
    { 
        return g_14[2];
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
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    for (i = 0; i < 4; i++)
    {
        transparent_crc(g_14[i], "g_14[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
