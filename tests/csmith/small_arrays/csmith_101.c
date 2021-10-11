// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_101.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-1L);
static uint8_t g_9[3] = {0x62L,0x62L,0x62L};



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint32_t l_6 = 0x7E17F759L;
    int32_t l_7 = 0xFBB4EBB0L;
    int32_t l_8 = (-1L);
    for (g_2 = 10; (g_2 <= (-6)); g_2 = safe_sub_func_int32_t_s_s(g_2, 3))
    { 
        return g_2;
    }
    l_8 = ((!(l_7 = l_6)) , (-10L));
    for (g_2 = 0; g_2 < 3; g_2 += 1)
    {
        g_9[g_2] = 0UL;
    }
    return l_7;
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    for (i = 0; i < 3; i++)
    {
        transparent_crc(g_9[i], "g_9[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
