// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_997.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x60477862L;
static int32_t g_5 = 0x974B666AL;
static int16_t g_6 = 9L;
static int64_t g_17 = 0xBB4F5AC3D6C1DFE9LL;
static int16_t g_18 = 0x1EB6L;
static int16_t g_20 = 0x75DAL;
static int16_t g_21 = (-10L);
static int32_t g_22 = 0x205300CEL;
static uint8_t g_25 = 0xC6L;



static uint16_t  func_1(void);
static uint64_t  func_30(uint32_t  p_31, int32_t  p_32, uint32_t  p_33, uint32_t  p_34);




static uint16_t  func_1(void)
{ 
    int8_t l_15 = 0x4FL;
    int32_t l_19 = 0x27F355C0L;
    int32_t l_23 = 1L;
    uint32_t l_64 = 0xCEB03922L;
    for (g_2 = (-13); (g_2 >= 18); g_2 = safe_add_func_int64_t_s_s(g_2, 1))
    { 
        uint32_t l_7 = 0x24C00011L;
        int32_t l_16 = 0x41AC3DC9L;
        int32_t l_24 = 0x6B5CFDA6L;
        g_5 = ((++l_7) >= (g_18 = (g_6 |= (((2L < ((0x3FF14EB4L & (g_17 = (safe_lshift_func_int16_t_s_u((+(safe_mul_func_int8_t_s_s(((l_15 < l_16) , g_2), 0xBEL))), 12)))) , 0x6DFCL)) , l_15) && g_2))));
        g_5 = l_16;
        g_25--;
        g_5 ^= g_22;
        l_23 |= (safe_sub_func_uint64_t_u_u(18446744073709551608UL, l_24));
        l_23 = (l_19 = (((func_30(l_24, g_25, l_16, g_17) , l_7) >= l_15) && l_7));
    }
    l_19 = ((safe_rshift_func_uint8_t_u_s(g_18, 5)) >= ((safe_rshift_func_uint8_t_u_u(1UL, 1)) , ((((g_20 == g_25) && l_19) > 1L) > l_19)));
    g_5 = (g_2 = (l_23 ^ (safe_rshift_func_uint8_t_u_u(g_18, l_19))));
    l_23 = ((((l_23 <= (g_21 <= ((safe_div_func_int8_t_s_s(((safe_sub_func_int64_t_s_s((safe_lshift_func_uint16_t_u_u((safe_lshift_func_uint16_t_u_s((l_64 && l_64), 10)), g_18)), g_2)) >= l_19), l_23)) && l_15))) == 0x0F61094BL) , g_6) == l_23);
    return g_21;
}



static uint64_t  func_30(uint32_t  p_31, int32_t  p_32, uint32_t  p_33, uint32_t  p_34)
{ 
    uint32_t l_37 = 4294967295UL;
    g_5 = ((g_25--) != l_37);
    for (g_17 = 0; (g_17 >= (-26)); g_17 = safe_sub_func_int8_t_s_s(g_17, 3))
    { 
        uint16_t l_44 = 0xB449L;
        int32_t l_45 = 0L;
        g_5 = ((((l_45 = ((g_20 = ((p_34 && ((((((((safe_mod_func_uint64_t_u_u((safe_add_func_uint8_t_u_u((l_44 , g_18), 0x2FL)), p_32)) < 0xA8L) != l_37) || l_37) , 2UL) != p_34) , 0L) == 1L)) == p_31)) && g_17)) != p_33) , g_5) > 0x7DDCL);
    }
    return g_18;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_17, "g_17", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_22, "g_22", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
