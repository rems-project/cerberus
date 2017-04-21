// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o gen/csmith_06.c
#include "csmith.h"


static long __undefined;



static int8_t g_9 = 0xAAL;
static uint32_t g_10 = 0xC4F3F7E8L;
static int32_t g_11 = 0x3825062DL;
static int16_t g_12 = 0x40CAL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    int32_t l_4 = 0xAFE01BD9L;
    int32_t l_5 = (-6L);
    int32_t l_13 = 6L;
    uint64_t l_18 = 0x46CD5FEC46BC2273LL;
    l_5 = (l_4 = (safe_div_func_uint32_t_u_u(4294967295UL, l_4)));
    l_13 &= ((g_12 = (g_11 = (~((((safe_add_func_uint8_t_u_u(((g_10 = ((0x59EEL & l_5) <= g_9)) > 0UL), l_5)) & l_4) >= l_4) <= g_9)))) || g_10);
    l_18 = (safe_mod_func_uint16_t_u_u(((safe_div_func_int32_t_s_s(g_12, 0xC4AEE507L)) & g_10), 0x59EAL));
    return g_12;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
