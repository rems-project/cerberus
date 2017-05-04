// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_255.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x462D5E48L;
static uint32_t g_5 = 0x8BAC04EEL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int32_t l_11 = 0xDCBA86BAL;
    int32_t l_13 = 0xEB2391CBL;
    for (g_2 = 0; (g_2 == (-7)); g_2 = safe_sub_func_uint32_t_u_u(g_2, 6))
    { 
        uint32_t l_12 = 1UL;
        g_5 = 0x61F66568L;
        for (g_5 = 16; (g_5 == 42); g_5 = safe_add_func_int16_t_s_s(g_5, 8))
        { 
            l_12 = ((safe_sub_func_uint64_t_u_u((safe_unary_minus_func_uint16_t_u(g_2)), g_2)) | l_11);
        }
    }
    l_13 = 1L;
    return g_5;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
