// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_936.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 0x14A0L;
static int64_t g_3 = 0x36951AD386CCE57BLL;
static uint64_t g_14 = 8UL;
static int32_t g_15 = 0xECE3051EL;
static uint32_t g_23 = 0UL;
static uint16_t g_37 = 1UL;
static uint8_t g_43 = 0xB5L;



static uint8_t  func_1(void);
static uint32_t  func_5(uint64_t  p_6, uint8_t  p_7, uint16_t  p_8, uint32_t  p_9, uint32_t  p_10);




static uint8_t  func_1(void)
{ 
    int32_t l_4 = (-10L);
    uint16_t l_17 = 4UL;
    int32_t l_44 = 0xF41AF53CL;
    g_3 |= (g_2 , g_2);
    if ((l_4 = (g_2 != l_4)))
    { 
        uint32_t l_16 = 0xB5542AFAL;
        int32_t l_41 = 1L;
        const uint8_t l_42 = 1UL;
        l_41 = ((func_5((safe_div_func_int8_t_s_s((g_15 = (g_14 = (+0xE4A6F44401D1B984LL))), l_16)), l_17, g_2, g_2, g_2) , 0x00B8L) & 0xEC76L);
        g_43 = l_42;
    }
    else
    { 
        l_44 |= (((l_4 && g_3) == (-8L)) | g_2);
    }
    return l_17;
}



static uint32_t  func_5(uint64_t  p_6, uint8_t  p_7, uint16_t  p_8, uint32_t  p_9, uint32_t  p_10)
{ 
    uint8_t l_21 = 5UL;
    int32_t l_32 = 0x6A81D68CL;
    int16_t l_40 = 0x534CL;
    if (((safe_rshift_func_int16_t_s_u(((~(p_9 , l_21)) > 0xA37D7C86L), l_21)) | g_14))
    { 
        uint16_t l_22 = 65535UL;
        int32_t l_33 = 0xFC786C7AL;
        int32_t l_34 = 0x73ED1322L;
        int32_t l_35 = 0xFD89D684L;
        int32_t l_36 = 0xEB927EEDL;
        l_22 = (g_2 & 1L);
        g_23 |= g_15;
        l_32 |= (safe_rshift_func_int16_t_s_s((safe_mod_func_uint16_t_u_u((safe_sub_func_uint8_t_u_u((safe_lshift_func_uint16_t_u_u(l_22, l_21)), p_7)), l_21)), p_8));
        --g_37;
    }
    else
    { 
        return g_2;
    }
    return l_40;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_37, "g_37", print_hash_value);
    transparent_crc(g_43, "g_43", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
