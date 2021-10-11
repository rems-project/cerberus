// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_270.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xA48BBCA6L;
static int32_t g_18[4] = {0xF3F6085EL,0xF3F6085EL,0xF3F6085EL,0xF3F6085EL};
static int16_t g_29 = (-9L);
static uint8_t g_31 = 255UL;
static uint32_t g_37 = 0x68927649L;



static int8_t  func_1(void);
static int32_t  func_5(int64_t  p_6, int8_t  p_7, uint8_t  p_8, uint32_t  p_9, int8_t  p_10);
static int16_t  func_25(int32_t  p_26);




static int8_t  func_1(void)
{ 
    uint64_t l_11 = 0xE77AB3921DED6804LL;
    int32_t l_27 = 0x3799040CL;
    int32_t l_28 = 0x1EE4CFF1L;
    int32_t l_30 = 0x7440271DL;
    for (g_2 = 0; (g_2 < (-17)); g_2 = safe_sub_func_uint8_t_u_u(g_2, 1))
    { 
        uint16_t l_16[4] = {0xC341L,0xC341L,0xC341L,0xC341L};
        int32_t l_19 = (-1L);
        int i;
        l_19 = (g_18[3] = func_5(l_11, g_2, (((safe_sub_func_int64_t_s_s((safe_mod_func_uint64_t_u_u(g_2, l_11)), g_2)) == l_16[1]) , 0x7AL), g_2, g_2));
        return g_2;
    }
    for (l_11 = (-3); (l_11 >= 56); ++l_11)
    { 
        uint16_t l_22 = 4UL;
        l_22++;
        if (g_18[3])
            continue;
        l_28 ^= (g_18[3] = ((g_37 &= func_25(((func_5(((g_31--) , g_29), (func_5(l_11, g_2, g_29, l_30, g_18[0]) <= (-1L)), l_22, g_18[3], l_27) >= g_18[0]) | 4UL))) , g_18[3]));
        return g_18[3];
    }
    return g_29;
}



static int32_t  func_5(int64_t  p_6, int8_t  p_7, uint8_t  p_8, uint32_t  p_9, int8_t  p_10)
{ 
    int64_t l_17 = 0x11BC383C67EE39F3LL;
    return l_17;
}



static int16_t  func_25(int32_t  p_26)
{ 
    int16_t l_34 = 1L;
    l_34 = p_26;
    for (g_2 = 21; (g_2 < 8); g_2--)
    { 
        return p_26;
    }
    return l_34;
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
    for (i = 0; i < 4; i++)
    {
        transparent_crc(g_18[i], "g_18[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_29, "g_29", print_hash_value);
    transparent_crc(g_31, "g_31", print_hash_value);
    transparent_crc(g_37, "g_37", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
