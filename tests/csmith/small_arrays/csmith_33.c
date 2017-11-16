// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_33.c
#include "csmith.h"


static long __undefined;



static int32_t g_2[1] = {(-7L)};
static int8_t g_3 = 0xDAL;
static int16_t g_20 = 4L;
static int32_t g_21[1] = {3L};
static int16_t g_25 = 1L;
static uint8_t g_27 = 0x0AL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int32_t l_9 = 0x9AE77AB3L;
    int8_t l_14 = (-1L);
    int32_t l_23 = 0x44D99649L;
    int32_t l_24 = 0x1DBCABEBL;
    g_3 ^= g_2[0];
    if (((safe_div_func_uint16_t_u_u((!(safe_rshift_func_int8_t_s_u(l_9, g_2[0]))), (((safe_rshift_func_int8_t_s_u(((safe_lshift_func_uint8_t_u_u(l_9, l_9)) && g_2[0]), 0)) & l_14) , g_3))) && g_2[0]))
    { 
        return g_2[0];
    }
    else
    { 
        uint64_t l_15 = 0xC67EE39F3FAA32F3LL;
        int32_t l_22 = 0xB91EE4CFL;
        int32_t l_26 = (-1L);
        l_9 = l_15;
        l_9 = 0xDD013D0BL;
        g_20 = (safe_lshift_func_int16_t_s_u(l_15, ((safe_sub_func_int64_t_s_s((g_2[0] == (l_14 <= l_15)), l_15)) == l_14)));
        g_27--;
    }
    return g_21[0];
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
    transparent_crc(g_20, "g_20", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_21[i], "g_21[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_25, "g_25", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
