// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_133.c
#include "csmith.h"


static long __undefined;



static int32_t g_2[4] = {1L,1L,1L,1L};
static int8_t g_17 = (-6L);



static const uint16_t  func_1(void);




static const uint16_t  func_1(void)
{ 
    int32_t l_7 = 0xA20A2982L;
    uint32_t l_11[3];
    int i;
    for (i = 0; i < 3; i++)
        l_11[i] = 1UL;
    for (g_2[3] = 0; (g_2[3] <= (-26)); g_2[3] = safe_sub_func_int8_t_s_s(g_2[3], 4))
    { 
        uint8_t l_8[1];
        int i;
        for (i = 0; i < 1; i++)
            l_8[i] = 250UL;
        l_8[0] = (((g_2[3] ^ (~((~65535UL) <= g_2[3]))) & 1L) & l_7);
    }
    if (((g_2[3] > ((safe_sub_func_int32_t_s_s(l_11[1], (~((safe_div_func_uint32_t_u_u(g_2[2], g_2[3])) , 0L)))) , g_2[1])) > l_11[1]))
    { 
        const int16_t l_15 = 0L;
        return l_15;
    }
    else
    { 
        int32_t l_16 = 0L;
        g_17 = (g_2[3] = l_16);
        return g_2[1];
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
        transparent_crc(g_2[i], "g_2[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_17, "g_17", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
