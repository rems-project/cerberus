// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_324.c
#include "csmith.h"


static long __undefined;



static int32_t g_7 = 0xD214C405L;
static uint8_t g_26 = 255UL;
static uint64_t g_30 = 18446744073709551615UL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int16_t l_6 = 0x83C8L;
    int32_t l_8 = (-1L);
    int16_t l_9 = 0x7A9AL;
    uint64_t l_14 = 0xB2391CB4E76AB2AELL;
    int8_t l_31 = (-6L);
    l_8 = (g_7 = (safe_mod_func_int32_t_s_s(((safe_add_func_uint32_t_u_u(4294967286UL, l_6)) , l_6), l_6)));
    l_9 = g_7;
    for (l_6 = 0; (l_6 <= 21); l_6 = safe_add_func_uint8_t_u_u(l_6, 3))
    { 
        uint8_t l_21 = 3UL;
        uint32_t l_22 = 0UL;
        int32_t l_25 = 0x72C40A98L;
        l_14 = (safe_sub_func_uint64_t_u_u(18446744073709551615UL, 0x7C9D5FAC12265E3ELL));
        for (l_8 = 0; (l_8 > 7); l_8++)
        { 
            g_7 = (safe_div_func_uint16_t_u_u((0x2278L | 8UL), g_7));
            g_7 = ((safe_lshift_func_int16_t_s_s((l_21 && l_22), l_9)) , l_21);
        }
        for (g_7 = 24; (g_7 >= 23); g_7 = safe_sub_func_uint32_t_u_u(g_7, 4))
        { 
            int32_t l_29 = 0x55A61940L;
            g_26--;
            g_30 ^= (((g_7 || 0xEE67L) , g_26) != l_29);
        }
    }
    l_31 ^= (g_7 = ((-2L) || g_7));
    return g_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_30, "g_30", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
