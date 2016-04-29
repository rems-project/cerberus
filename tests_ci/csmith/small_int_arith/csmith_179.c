// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_179.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x824A8C6AL;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int64_t l_12 = 0x10789328A062B000LL;
    int32_t l_13 = 6L;
    int32_t l_15 = 9L;
    for (g_2 = 0; (g_2 >= 9); ++g_2)
    { 
        uint16_t l_5 = 65535UL;
        int32_t l_14 = 1L;
        --l_5;
        l_14 = ((safe_mod_func_int8_t_s_s(((safe_add_func_int64_t_s_s((l_12 = ((0x9CB61D2250DB8561LL != g_2) & g_2)), 0x9D75405732AA61FCLL)) | (-6L)), l_13)) < 1UL);
        if (l_14)
            continue;
    }
    l_15 = ((((((255UL && l_13) , l_13) , g_2) < l_12) < l_13) ^ g_2);
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
