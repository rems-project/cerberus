// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_364.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2[4] = {4UL,4UL,4UL,4UL};
static int32_t g_13 = 0xB65720B9L;
static uint8_t g_14[1] = {255UL};
static uint64_t g_15[2] = {0x66D210EC3203BD65LL,0x66D210EC3203BD65LL};
static int16_t g_19 = 0xC821L;
static uint32_t g_27 = 2UL;
static int32_t g_33[1] = {(-1L)};



static uint8_t  func_1(void);
static int8_t  func_3(int8_t  p_4, uint64_t  p_5, int32_t  p_6, int32_t  p_7);




static uint8_t  func_1(void)
{ 
    int16_t l_8 = 0xF8F0L;
    int32_t l_20 = 0x120DD93BL;
    int32_t l_24 = 9L;
    int16_t l_30 = 1L;
    int32_t l_41[3];
    int i;
    for (i = 0; i < 3; i++)
        l_41[i] = 6L;
    g_15[0] |= (g_14[0] = (g_2[0] & (1UL < (g_13 |= func_3(l_8, g_2[0], l_8, g_2[0])))));
    g_13 = 0L;
    for (l_8 = 0; l_8 < 4; l_8 += 1)
    {
        g_2[l_8] = 0xAAF0A9B27FA3DFADLL;
    }
    for (l_8 = 0; (l_8 <= 1); l_8 += 1)
    { 
        uint8_t l_16 = 0x1BL;
        int32_t l_17 = 0xE7C14AB6L;
        int32_t l_18 = (-3L);
        int i;
        l_20 &= (g_19 = (l_18 = (l_17 = (g_13 |= ((l_16 = 1L) ^ g_15[l_8])))));
        l_20 = (g_15[l_8] && ((func_3(l_20, l_8, l_17, l_16) , 0x32D3L) > 0xA8C9L));
    }
    for (l_8 = 0; (l_8 != 29); l_8 = safe_add_func_uint64_t_u_u(l_8, 1))
    { 
        uint8_t l_23[1];
        int32_t l_28 = 0xF8BA7967L;
        int32_t l_29 = 0xBFEED1B4L;
        int i;
        for (i = 0; i < 1; i++)
            l_23[i] = 0x74L;
        l_24 ^= ((g_15[1] = (l_20 |= l_23[0])) ^ g_14[0]);
        l_29 &= func_3((g_15[1] != (safe_rshift_func_uint16_t_u_u(l_23[0], 2))), (l_28 = ((g_27 = 0xDCL) > g_2[0])), g_19, l_24);
        l_29 = g_15[1];
        if (g_14[0])
            break;
        l_30 = 1L;
        return l_28;
    }
    for (g_27 = 0; (g_27 <= 1); g_27 += 1)
    { 
        int i;
        return g_2[(g_27 + 2)];
    }
    for (l_8 = 0; (l_8 <= (-5)); l_8--)
    { 
        uint32_t l_34 = 0x0A061FA4L;
        --l_34;
        if (g_13)
            continue;
    }
    g_13 = ((safe_mul_func_uint8_t_u_u((g_33[0] == g_14[0]), (safe_rshift_func_int16_t_s_u(func_3(l_41[2], g_13, g_33[0], l_30), l_20)))) || 255UL);
    return l_8;
}



static int8_t  func_3(int8_t  p_4, uint64_t  p_5, int32_t  p_6, int32_t  p_7)
{ 
    uint32_t l_11 = 4294967287UL;
    int32_t l_12 = (-3L);
    l_12 = (safe_lshift_func_int8_t_s_s(l_11, 3));
    return l_12;
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
    transparent_crc(g_13, "g_13", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_14[i], "g_14[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    for (i = 0; i < 2; i++)
    {
        transparent_crc(g_15[i], "g_15[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_33[i], "g_33[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
