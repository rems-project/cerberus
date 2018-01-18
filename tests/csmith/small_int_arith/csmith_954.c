// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_954.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x8EAC8B13L;
static int64_t g_16 = 0x1E283D1F0DFBC43CLL;
static int32_t g_18 = (-1L);
static uint64_t g_19 = 0x7C3B7C39C9D94031LL;
static uint32_t g_22 = 9UL;
static int64_t g_23 = 1L;
static int32_t g_24 = 0x79339B88L;
static uint16_t g_25 = 3UL;
static int64_t g_39 = 7L;
static uint64_t g_40 = 0x0190438315EAC84CLL;



static uint32_t  func_1(void);
static int32_t  func_5(uint32_t  p_6, uint64_t  p_7);




static uint32_t  func_1(void)
{ 
    uint32_t l_11 = 4294967287UL;
    int32_t l_28 = (-10L);
    int32_t l_29 = 0x3C17A3F0L;
    const uint64_t l_33 = 0UL;
    for (g_2 = (-2); (g_2 > (-4)); --g_2)
    { 
        int64_t l_12 = 0x61EEFB6F65E790E8LL;
        int32_t l_13 = 8L;
        l_13 = func_5(((safe_lshift_func_uint8_t_u_u(((~((((l_12 = (g_2 == l_11)) , 1L) > 0x35L) < g_2)) & 0UL), 0)) & l_11), l_13);
        g_25++;
        if (g_19)
            continue;
        if (g_18)
            break;
    }
lbl_32:
    l_29 = (l_28 = (65527UL || l_11));
    for (g_23 = 0; (g_23 >= 26); g_23 = safe_add_func_uint8_t_u_u(g_23, 1))
    { 
        if (g_18)
            goto lbl_32;
    }
    if (((((g_2 , g_2) >= g_18) , l_33) , l_28))
    { 
        int16_t l_34 = 7L;
        g_24 = l_34;
    }
    else
    { 
        int32_t l_35 = (-5L);
        int32_t l_36 = (-1L);
        int32_t l_37 = 0x96BC97DEL;
        int32_t l_38 = 0xD4AD4463L;
        g_2 = ((3L || 65535UL) == g_22);
        if (l_11)
            goto lbl_43;
        --g_40;
lbl_43:
        g_24 = g_39;
        g_24 = ((g_2 , g_25) >= l_33);
    }
    return g_40;
}



static int32_t  func_5(uint32_t  p_6, uint64_t  p_7)
{ 
    int8_t l_14 = 0L;
    int32_t l_15 = 1L;
    int32_t l_17 = 8L;
    l_15 ^= ((g_2 ^ l_14) , g_2);
    l_17 = (((g_16 &= ((l_15 = 0x04157736D0C11E04LL) <= 8L)) > 0L) != p_6);
    g_19--;
    g_22 = (l_15 >= l_17);
    return g_19;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    transparent_crc(g_39, "g_39", print_hash_value);
    transparent_crc(g_40, "g_40", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
