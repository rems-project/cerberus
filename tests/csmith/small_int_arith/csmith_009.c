// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o gen/csmith_09.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 0x7FA5C62EL;
static uint64_t g_7 = 0x4EB4C8F0D0714AD3LL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint32_t l_2 = 0xC2039807L;
    int32_t l_4 = 0L;
    l_4 = (((l_2 , g_3) <= g_3) >= l_2);
    g_7 ^= ((safe_mul_func_int8_t_s_s((((l_2 , (-7L)) ^ l_4) , 0x49L), g_3)) == g_3);
    return l_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
