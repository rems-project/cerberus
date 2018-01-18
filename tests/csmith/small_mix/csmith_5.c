// Options:   --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 5 --max-expr-complexity 4 --max-funcs 5 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_5.c
#include "csmith.h"


static long __undefined;


union U0 {
   const int8_t * f0;
   const int32_t  f1;
};


static int32_t g_4 = (-5L);
static int16_t g_18 = 0xD018L;
static uint64_t g_19 = 0x88039D6B9C2D621ELL;
static union U0 g_22 = {0};



static union U0  func_1(void);




static union U0  func_1(void)
{ 
    int64_t l_2 = (-8L);
    int32_t *l_3 = &g_4;
    int32_t *l_5 = (void*)0;
    int32_t *l_6 = &g_4;
    int32_t *l_7 = &g_4;
    int32_t *l_8 = &g_4;
    int32_t *l_9 = (void*)0;
    int32_t *l_10 = &g_4;
    int32_t *l_11 = (void*)0;
    int32_t *l_12 = &g_4;
    int32_t *l_13 = (void*)0;
    int32_t *l_14 = &g_4;
    int32_t l_15 = 1L;
    int32_t *l_16 = &l_15;
    int32_t *l_17[2];
    int i;
    for (i = 0; i < 2; i++)
        l_17[i] = &l_15;
    g_19--;
    l_13 = &g_4;
    return g_22;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
