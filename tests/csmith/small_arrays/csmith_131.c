// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_131.c
#include "csmith.h"


static long __undefined;



static int32_t g_2[1] = {(-1L)};
static int32_t g_3 = 0x0DA11525L;
static uint32_t g_4[3] = {0x5165352FL,0x5165352FL,0x5165352FL};
static uint64_t g_22[1] = {0UL};
static int32_t g_23[3] = {0x8E01AFECL,0x8E01AFECL,0x8E01AFECL};



static const int32_t  func_1(void);
static uint16_t  func_5(uint64_t  p_6);




static const int32_t  func_1(void)
{ 
    uint8_t l_21 = 0UL;
    for (g_3 = 0; (g_3 >= 0); g_3 -= 1)
    { 
        int i;
        if (g_2[g_3])
            break;
        if (g_2[0])
            continue;
    }
    g_23[1] &= ((g_22[0] ^= (((g_4[0] |= 0x65E08CCCDDD1D8F8LL) > (func_5((g_2[0] > (safe_lshift_func_uint16_t_u_s(((~((safe_lshift_func_int8_t_s_u((~g_2[0]), 1)) , 2L)) , 0x22BAL), g_2[0])))) <= 8L)) != l_21)) > l_21);
    return l_21;
}



static uint16_t  func_5(uint64_t  p_6)
{ 
    uint32_t l_13 = 0UL;
    int32_t l_14 = 0x89BDD777L;
    int32_t l_15 = (-1L);
    int32_t l_16 = 0xF27A4129L;
    int32_t l_17[2];
    uint64_t l_18 = 0x9628EAF6082F4E55LL;
    int i;
    for (i = 0; i < 2; i++)
        l_17[i] = 0xFC42FF18L;
    l_13 = g_3;
    ++l_18;
    l_15 = 0x58D0336DL;
    l_15 = 0x5BF7C295L;
    return g_2[0];
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_2[i], "g_2[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_3, "g_3", print_hash_value);
    for (i = 0; i < 3; i++)
    {
        transparent_crc(g_4[i], "g_4[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_22[i], "g_22[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    for (i = 0; i < 3; i++)
    {
        transparent_crc(g_23[i], "g_23[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
