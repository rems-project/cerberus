// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_207.c
#include "csmith.h"


static long __undefined;



static int32_t g_2[4] = {(-1L),(-1L),(-1L),(-1L)};
static uint16_t g_10 = 65529UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_6 = 0xDB8FAAAEL;
    int32_t l_7 = 5L;
    int32_t l_8 = 0xD6804445L;
    int32_t l_13[1];
    int16_t l_14 = 4L;
    int64_t l_15 = 1L;
    uint32_t l_16[2];
    int i;
    for (i = 0; i < 1; i++)
        l_13[i] = 0x52733582L;
    for (i = 0; i < 2; i++)
        l_16[i] = 5UL;
    for (g_2[1] = 0; (g_2[1] >= (-16)); g_2[1]--)
    { 
        int64_t l_5 = (-3L);
        int32_t l_9 = (-3L);
        g_10--;
    }
    l_16[0]++;
    return l_8;
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
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
