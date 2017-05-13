// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_241.c
#include "csmith.h"


static long __undefined;



static int64_t g_3 = 0xFCF09CC25FA5FEF9LL;
static int32_t g_6 = 0x25F5F996L;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int32_t l_2 = 0x1C2A2C7CL;
    if ((((((l_2 , l_2) | 0xA1BFL) && g_3) > l_2) != l_2))
    { 
        return l_2;
    }
    else
    { 
        int32_t l_11 = 0L;
        g_6 = (safe_mod_func_int8_t_s_s(g_3, g_3));
        l_2 |= g_3;
        l_2 = (safe_div_func_int64_t_s_s(g_6, g_3));
        l_11 = ((safe_div_func_uint32_t_u_u((l_2 , g_3), g_6)) > g_3);
    }
    return g_6;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
