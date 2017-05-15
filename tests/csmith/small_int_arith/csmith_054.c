// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_054.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 3L;
static int8_t g_20 = 0x86L;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint64_t l_3 = 0x5664DC9ED9BA07E4LL;
    int32_t l_4 = 0xFAAFE30FL;
    l_4 |= (((g_2 != g_2) <= g_2) < l_3);
    for (l_4 = (-4); (l_4 <= (-29)); --l_4)
    { 
        uint8_t l_15 = 0xB8L;
        int32_t l_18 = 0x3DDCA272L;
        int32_t l_19 = 0xF3CCD246L;
        g_2 = ((safe_lshift_func_uint8_t_u_u(((safe_mod_func_int8_t_s_s((safe_rshift_func_uint8_t_u_u((g_20 = (l_19 &= (safe_sub_func_uint32_t_u_u((l_15--), (((0L > g_2) , l_18) , g_2))))), 4)), g_2)) < l_18), g_2)) , g_20);
        l_19 = (safe_mod_func_uint8_t_u_u((safe_mod_func_int32_t_s_s((safe_div_func_int8_t_s_s(0L, 0xAAL)), g_20)), 0xA9L));
    }
    return l_3;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
