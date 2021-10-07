// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_97.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = 0xECL;
static uint32_t g_3[2] = {0x124F84B8L,0x124F84B8L};
static uint32_t g_5 = 4294967295UL;
static uint64_t g_6 = 0x1B055CC25BFC88EBLL;
static uint64_t g_26 = 18446744073709551615UL;
static uint32_t g_34[1] = {8UL};
static uint8_t g_39 = 0x22L;
static uint64_t g_41[3] = {9UL,9UL,9UL};
static int16_t g_49 = 0xF28DL;
static int16_t g_50 = 0x7BB5L;



static uint64_t  func_1(void);
static uint32_t  func_13(int16_t  p_14);
static int32_t  func_17(int8_t  p_18, uint32_t  p_19);




static uint64_t  func_1(void)
{ 
    int32_t l_25 = (-1L);
    if ((1L <= (-10L)))
    { 
        int32_t l_4 = 7L;
        g_3[1] = g_2;
        l_4 = g_2;
    }
    else
    { 
        int32_t l_24 = 0xB058EFA9L;
        int32_t l_33 = 0xD08F4923L;
        g_5 = g_3[1];
        g_6 = 0x3F365653L;
        g_26 = (safe_mul_func_uint16_t_u_u((((l_25 = (safe_lshift_func_uint8_t_u_u((safe_div_func_uint32_t_u_u(func_13((safe_div_func_int32_t_s_s(func_17(((0x19F2L > 0L) < g_2), g_5), 0x350D8AF8L))), l_24)), g_3[1]))) != 0xAB56411DL) || l_25), g_2));
        g_34[0] |= (safe_rshift_func_uint8_t_u_s((safe_mod_func_int16_t_s_s((((((l_24 = (safe_lshift_func_uint8_t_u_u(((1UL != l_24) == l_25), 0))) < 1L) , 0x0D58L) != l_33) , (-1L)), l_25)), 4));
        return l_25;
    }
    for (g_2 = 0; (g_2 < (-22)); g_2 = safe_sub_func_uint8_t_u_u(g_2, 9))
    { 
        uint64_t l_40 = 18446744073709551615UL;
        int32_t l_48 = (-1L);
        g_39 = (safe_mul_func_int16_t_s_s((18446744073709551615UL != g_6), g_26));
        l_40 = g_2;
        g_41[1]--;
        g_50 |= (0x3AL > (safe_add_func_int64_t_s_s((g_26 > ((g_49 &= func_17(((safe_lshift_func_int16_t_s_s((0x61L >= l_48), 10)) ^ g_26), g_39)) <= l_25)), 0x6F8A3E09E13A3A1BLL)));
    }
    return g_26;
}



static uint32_t  func_13(int16_t  p_14)
{ 
    uint64_t l_21 = 0UL;
    l_21--;
    return l_21;
}



static int32_t  func_17(int8_t  p_18, uint32_t  p_19)
{ 
    int8_t l_20 = 0xEDL;
    return l_20;
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
    for (i = 0; i < 2; i++)
    {
        transparent_crc(g_3[i], "g_3[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_34[i], "g_34[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_39, "g_39", print_hash_value);
    for (i = 0; i < 3; i++)
    {
        transparent_crc(g_41[i], "g_41[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_49, "g_49", print_hash_value);
    transparent_crc(g_50, "g_50", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
