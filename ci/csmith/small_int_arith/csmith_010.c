// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o gen/csmith_10.c
#include "csmith.h"


static long __undefined;



static int8_t g_8 = 0x8FL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint16_t l_7 = 0UL;
    int32_t l_9 = 0xF90EF307L;
    int32_t l_10 = 0x88E17B84L;
    uint8_t l_11 = 0xCFL;
    int8_t l_20 = 0x4CL;
    l_10 = (l_9 = ((safe_sub_func_uint8_t_u_u((!(safe_rshift_func_uint16_t_u_u(((l_7 <= l_7) , g_8), 10))), (-1L))) || g_8));
    if (l_11)
    { 
        int32_t l_14 = 0x203BD652L;
        l_14 &= ((safe_mod_func_uint16_t_u_u(g_8, l_11)) , 0xFE23A266L);
    }
    else
    { 
        int8_t l_15 = 0xD4L;
        int32_t l_16 = (-7L);
        l_15 |= g_8;
        l_16 |= l_11;
    }
    l_9 = (safe_lshift_func_uint16_t_u_u((!g_8), l_11));
    l_20 ^= (0x717F4039EE491BA6LL < l_9);
    return g_8;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_8, "g_8", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
