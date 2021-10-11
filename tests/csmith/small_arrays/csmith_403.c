// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_403.c
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 1L;
static int32_t g_7[1] = {(-1L)};
static uint16_t g_22 = 1UL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int32_t l_2[3];
    int32_t l_6 = 1L;
    int32_t l_8 = (-6L);
    int32_t l_11[2];
    int32_t l_13 = (-5L);
    int64_t l_29 = 1L;
    uint16_t l_31 = 0xFC40L;
    int i;
    for (i = 0; i < 3; i++)
        l_2[i] = 0x41B3C692L;
    for (i = 0; i < 2; i++)
        l_11[i] = 0L;
    for (g_3 = 0; (g_3 <= 2); g_3 += 1)
    { 
        int32_t l_9 = 1L;
        int32_t l_10 = 0xD585ED06L;
        int32_t l_12 = 0x34688073L;
        int32_t l_14 = 0xC7E43439L;
        int32_t l_15 = 0xD70CADD6L;
        int32_t l_16 = 1L;
        int32_t l_17 = 1L;
        int32_t l_18[2];
        uint16_t l_19 = 3UL;
        int8_t l_28 = 0xABL;
        int64_t l_30 = 0x911B6BEFC5446ED9LL;
        int i;
        for (i = 0; i < 2; i++)
            l_18[i] = 0x881826FBL;
        g_7[0] = (safe_lshift_func_uint16_t_u_s((l_2[g_3] && (l_6 = g_3)), 5));
        --l_19;
        l_14 = (((g_22 = (l_11[1] ^= 0xCD538770L)) && ((((~(safe_rshift_func_uint16_t_u_u((g_22 <= (8UL < l_11[1])), 3))) > 0L) >= 0x38C8A251ABE719C2LL) < 0xDA1E1CF2BBA2D3C5LL)) , 0x9F111191L);
        if (g_7[0])
            break;
        l_12 = (l_17 &= (safe_lshift_func_uint16_t_u_u(0xFFAEL, 12)));
        l_31++;
    }
    return g_22;
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
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_7[i], "g_7[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_22, "g_22", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
