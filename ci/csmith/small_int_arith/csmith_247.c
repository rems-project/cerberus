// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_247.c
#include "csmith.h"


static long __undefined;



static uint32_t g_3 = 18446744073709551615UL;
static uint32_t g_4 = 0x715F0ED1L;
static int32_t g_5 = 0x4BEDCC59L;
static int16_t g_7 = 0xD711L;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint64_t l_2 = 0x832937A3A11C1574LL;
    int32_t l_6 = (-9L);
    int32_t l_8 = 0x44CACFF8L;
    l_8 = (((((l_6 = (g_5 = (g_4 = (g_3 = l_2)))) && g_5) && g_4) <= 0x60F7L) >= g_7);
    return l_2;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
