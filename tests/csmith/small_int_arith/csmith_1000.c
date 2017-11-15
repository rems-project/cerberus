// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1000.c
#include "csmith.h"


static long __undefined;



static int32_t g_4 = 4L;
static int16_t g_19 = 6L;
static uint8_t g_37 = 246UL;
static int16_t g_38 = (-1L);



static uint32_t  func_1(void);
static const uint16_t  func_22(uint8_t  p_23, int32_t  p_24, uint64_t  p_25, int8_t  p_26);




static uint32_t  func_1(void)
{ 
    int8_t l_3 = 0x66L;
    int32_t l_17 = 0x78F1E0C8L;
    int64_t l_36 = (-1L);
    if (((~l_3) ^ g_4))
    { 
        uint32_t l_7 = 4294967288UL;
        int32_t l_8 = 1L;
        l_8 = (safe_sub_func_int8_t_s_s(l_3, (l_7 && (((l_3 == g_4) >= (-1L)) , 254UL))));
    }
    else
    { 
        uint32_t l_18 = 0xD1B71362L;
        uint32_t l_29 = 0xCFD8F271L;
        g_19 |= (safe_mul_func_int16_t_s_s(0L, (safe_rshift_func_uint16_t_u_s((safe_rshift_func_uint8_t_u_s(l_3, 2)), ((safe_lshift_func_int16_t_s_s((l_17 = 0xF4E1L), l_18)) , g_4)))));
        l_17 = (((0x7FL < (func_22(g_4, (safe_div_func_uint64_t_u_u(18446744073709551615UL, l_29)), l_18, g_4) != g_19)) == l_17) , g_19);
        g_37 = ((safe_add_func_int64_t_s_s((((safe_sub_func_uint8_t_u_u(l_3, l_29)) != ((safe_mod_func_int64_t_s_s(((((((l_18 ^ 255UL) <= g_4) ^ l_29) < 65535UL) >= l_3) == 0L), 0x597A0B8914BE495ELL)) | l_36)) , l_17), g_4)) || g_4);
        g_38 ^= g_37;
    }
    return l_17;
}



static const uint16_t  func_22(uint8_t  p_23, int32_t  p_24, uint64_t  p_25, int8_t  p_26)
{ 
    return p_26;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_37, "g_37", print_hash_value);
    transparent_crc(g_38, "g_38", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
