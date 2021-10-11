// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_82.c
#include "csmith.h"


static long __undefined;



static int32_t g_3[4] = {0x860B4FFBL,0x860B4FFBL,0x860B4FFBL,0x860B4FFBL};
static uint16_t g_5 = 65529UL;
static int32_t g_16 = 0x8DDAC0FAL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int32_t l_2[3];
    int i;
    for (i = 0; i < 3; i++)
        l_2[i] = (-2L);
    for (g_3[2] = 2; (g_3[2] >= 0); g_3[2] -= 1)
    { 
        int32_t l_4 = 1L;
        uint32_t l_12 = 0xAAB72B21L;
        uint32_t l_15 = 18446744073709551607UL;
        --g_5;
        g_16 = (l_4 = (((safe_div_func_int16_t_s_s(((safe_sub_func_int64_t_s_s(l_12, (g_3[2] < (safe_sub_func_int64_t_s_s((((l_15 = (l_2[2] ^ g_3[3])) || 0x8586FD5DL) && l_4), 0x0A4CCFD66C4A87FCLL))))) || 5L), g_5)) >= 0xDEL) , l_2[0]));
        return g_16;
    }
    return l_2[2];
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
        transparent_crc(g_3[i], "g_3[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
