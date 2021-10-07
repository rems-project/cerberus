// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_192.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 0xB5F5C184L;
static int32_t g_6 = 0x0BA1BF2BL;
static int8_t g_7 = 0L;
static uint64_t g_10 = 0x6544D1878ABC106ELL;
static int32_t g_15[3] = {0x488F4F36L,0x488F4F36L,0x488F4F36L};



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint16_t l_2[2];
    int32_t l_8 = 1L;
    int32_t l_14[3];
    uint16_t l_17[1];
    int i;
    for (i = 0; i < 2; i++)
        l_2[i] = 0x5B57L;
    for (i = 0; i < 3; i++)
        l_14[i] = 9L;
    for (i = 0; i < 1; i++)
        l_17[i] = 6UL;
    for (g_3 = 0; g_3 < 2; g_3 += 1)
    {
        l_2[g_3] = 0UL;
    }
lbl_22:
    for (g_3 = (-6); (g_3 <= (-14)); --g_3)
    { 
        int64_t l_9 = 1L;
        int32_t l_13 = 0x77CC4247L;
        int32_t l_16 = 1L;
        ++g_10;
        l_8 &= (-2L);
        g_6 = g_7;
        --l_17[0];
        g_15[0] |= 0x74ADF298L;
    }
    for (l_8 = (-8); (l_8 >= 11); l_8++)
    { 
        if (g_10)
            goto lbl_22;
    }
    return l_14[1];
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    for (i = 0; i < 3; i++)
    {
        transparent_crc(g_15[i], "g_15[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
