// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_213.c
#include "csmith.h"


static long __undefined;



static int64_t g_6[4] = {0x80E3580D416DB6D0LL,0x80E3580D416DB6D0LL,0x80E3580D416DB6D0LL,0x80E3580D416DB6D0LL};
static uint64_t g_8 = 0UL;
static uint64_t g_10[4] = {0x5E3B372BA29F5838LL,0x5E3B372BA29F5838LL,0x5E3B372BA29F5838LL,0x5E3B372BA29F5838LL};



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_5[3];
    int64_t l_7[4];
    int i;
    for (i = 0; i < 3; i++)
        l_5[i] = (-7L);
    for (i = 0; i < 4; i++)
        l_7[i] = 4L;
    if ((safe_add_func_int8_t_s_s(2L, (((~l_5[0]) , (((g_8 &= ((g_6[0] != 18446744073709551608UL) && l_7[3])) < g_6[0]) ^ 9L)) , 0x9FL))))
    { 
        uint16_t l_9 = 0xB164L;
        return l_9;
    }
    else
    { 
        --g_10[3];
        return g_6[1];
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
    for (i = 0; i < 4; i++)
    {
        transparent_crc(g_6[i], "g_6[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_8, "g_8", print_hash_value);
    for (i = 0; i < 4; i++)
    {
        transparent_crc(g_10[i], "g_10[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
