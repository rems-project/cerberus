// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_952.c
#include "csmith.h"


static long __undefined;



static uint64_t g_7 = 18446744073709551611UL;
static uint8_t g_20 = 0UL;
static int32_t g_21 = 0xEE973417L;
static int32_t g_24 = (-9L);
static uint32_t g_26 = 4294967293UL;
static uint64_t g_29 = 0xA2B8EA2C39D5B611LL;
static uint16_t g_35 = 65528UL;
static int32_t g_39 = (-4L);



static uint32_t  func_1(void);
static int32_t  func_2(uint32_t  p_3, uint32_t  p_4);




static uint32_t  func_1(void)
{ 
    int64_t l_40 = 9L;
    if (func_2((safe_add_func_uint16_t_u_u(65528UL, 1L)), g_7))
    { 
        g_21 = (((((safe_sub_func_uint16_t_u_u(0UL, g_20)) >= 0x707E294BL) , g_39) > l_40) <= 0x52DED1456B8642E5LL);
    }
    else
    { 
        int64_t l_45 = 0x444C9CADCDA6A44FLL;
        g_21 = (safe_mod_func_uint32_t_u_u(((((safe_sub_func_uint32_t_u_u(l_40, g_21)) == 0x826422F8L) >= g_26) & 0xFCE95866L), l_40));
        return l_45;
    }
    return l_40;
}



static int32_t  func_2(uint32_t  p_3, uint32_t  p_4)
{ 
    uint32_t l_9 = 7UL;
    int32_t l_10 = 0x0585B7F3L;
    int32_t l_22 = 0x7A329EF4L;
    int32_t l_23 = 0x7609FA85L;
    uint16_t l_34 = 1UL;
    if ((((+(l_10 &= l_9)) , l_9) >= 0x8E1BL))
    { 
        int16_t l_19 = (-7L);
        g_21 = (safe_div_func_uint32_t_u_u((g_20 &= (((safe_mod_func_uint16_t_u_u((safe_sub_func_uint8_t_u_u((safe_lshift_func_int8_t_s_u(g_7, 2)), l_19)), p_4)) != p_4) <= g_7)), l_9));
    }
    else
    { 
        int32_t l_25 = 0xBC248910L;
        uint16_t l_36 = 65529UL;
        g_26--;
        g_29++;
        l_36 = (safe_mod_func_int64_t_s_s((g_35 = l_34), p_3));
    }
    return g_20;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_24, "g_24", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_29, "g_29", print_hash_value);
    transparent_crc(g_35, "g_35", print_hash_value);
    transparent_crc(g_39, "g_39", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
