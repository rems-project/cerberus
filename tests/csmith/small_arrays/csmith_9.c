// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_9.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static int32_t g_11 = 0x009CE456L;
static int32_t g_22 = 1L;
static int32_t g_24[3] = {0x81720D70L,0x81720D70L,0x81720D70L};
static uint32_t g_36[1] = {0x504ED09EL};



static int8_t  func_1(void);
static int8_t  func_12(uint32_t  p_13, const int64_t  p_14, uint32_t  p_15, int8_t  p_16);




static int8_t  func_1(void)
{ 
    uint16_t l_10 = 4UL;
    int16_t l_23 = 9L;
    int32_t l_34[1];
    int i;
    for (i = 0; i < 1; i++)
        l_34[i] = 0L;
    for (g_2 = (-11); (g_2 >= (-29)); --g_2)
    { 
        int16_t l_21 = 0xB61BL;
        uint32_t l_29 = 0UL;
        int32_t l_32 = 0L;
        int32_t l_33 = 0xE4C7BA3FL;
        int32_t l_35 = 0x3ACDD711L;
        g_24[2] |= (0x73EB905D09EA9831LL <= (safe_add_func_int32_t_s_s((l_23 = (safe_unary_minus_func_uint32_t_u(((safe_mod_func_uint8_t_u_u((g_11 = l_10), (g_22 = func_12((safe_lshift_func_int8_t_s_s((safe_lshift_func_int8_t_s_s((g_2 , l_21), 0)), 5)), g_2, g_2, g_2)))) , 0xA8BC07C2L)))), l_10)));
        g_22 = (safe_mul_func_int8_t_s_s(l_21, func_12(l_10, (safe_lshift_func_uint8_t_u_u(252UL, l_21)), g_2, l_10)));
        l_29--;
        g_36[0]++;
        return l_35;
    }
    return g_24[2];
}



static int8_t  func_12(uint32_t  p_13, const int64_t  p_14, uint32_t  p_15, int8_t  p_16)
{ 
    return p_14;
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
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    for (i = 0; i < 3; i++)
    {
        transparent_crc(g_24[i], "g_24[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_36[i], "g_36[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
