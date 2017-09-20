// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_098.c
#include "csmith.h"


static long __undefined;



static int16_t g_4 = 0x0647L;
static uint32_t g_5 = 0x921DED68L;
static uint8_t g_7 = 248UL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    int32_t l_6 = 0xEDBDA7FEL;
    g_5 = ((safe_add_func_uint64_t_u_u((g_4 || 0x65ABL), 18446744073709551608UL)) , 0xFAAAEB9AL);
    g_7 = ((l_6 = g_4) , l_6);
    return g_4;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
