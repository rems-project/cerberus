// Options:   --arrays --no-bitfields --checksum --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --safe-math --no-packed-struct --no-pointers --no-structs --no-unions --no-volatiles --no-volatile-pointers --no-const-pointers --concise
#include "csmith.h"


static long __undefined;



static uint32_t g_13 = 5UL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    uint32_t l_2 = 0x93B4E1A3L;
    int32_t l_14 = 0x3E31551DL;
    int32_t l_15 = 0x0ED3C15DL;
    l_2--;
    l_15 ^= (safe_mul_func_int8_t_s_s((safe_add_func_uint16_t_u_u((safe_mul_func_uint8_t_u_u(((safe_mod_func_uint64_t_u_u((l_14 &= g_13), g_13)) == 0x49CEC79E672CA3C0LL), l_2)), g_13)), 0xADL));
    l_15 = (g_13 , g_13);
    return g_13;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
