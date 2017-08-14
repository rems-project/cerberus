// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_347.c
#include "csmith.h"


static long __undefined;



static uint32_t g_5 = 0x4F2887CFL;
static int8_t g_7 = 1L;
static int8_t g_8 = 0L;
static uint32_t g_9 = 0x345FE46CL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint32_t l_4 = 0x0E446DF3L;
    int32_t l_6 = 0x0F5872D9L;
    l_6 = (((safe_mod_func_int16_t_s_s((l_4 , g_5), l_4)) | 5L) <= 1L);
    g_9++;
    return l_4;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
