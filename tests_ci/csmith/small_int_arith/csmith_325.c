// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_325.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-4L);



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint64_t l_3 = 1UL;
    int32_t l_4 = (-9L);
    l_4 = ((g_2 || 0x5F1DBECCCE1E2C0DLL) | l_3);
    l_4 = ((safe_sub_func_int64_t_s_s((~0xD8F6L), g_2)) < l_3);
    l_4 = ((safe_lshift_func_uint8_t_u_u(0xC7L, l_4)) ^ g_2);
    return g_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
