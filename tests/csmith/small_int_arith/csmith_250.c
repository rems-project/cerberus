// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_250.c
#include "csmith.h"


static long __undefined;



static int8_t g_5 = 0xB7L;
static uint8_t g_7 = 0xBFL;
static int64_t g_8 = 0x5ED0657689A5A40FLL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int64_t l_4 = 5L;
    int32_t l_6 = 0xB9DD952EL;
    int8_t l_9 = (-1L);
    l_6 = (((safe_rshift_func_uint16_t_u_s((l_4 ^ l_4), 15)) , g_5) , 0xC6338430L);
    g_7 = (l_4 & 1UL);
    g_8 = (g_5 | l_6);
    return l_9;
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
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
