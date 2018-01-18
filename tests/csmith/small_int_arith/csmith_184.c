// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_184.c
#include "csmith.h"


static long __undefined;



static uint32_t g_5 = 0UL;
static int8_t g_6 = 0x09L;
static uint32_t g_9 = 0UL;
static uint64_t g_14 = 3UL;
static int64_t g_19 = 1L;
static int32_t g_29 = (-1L);



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint64_t l_4 = 0x5596960F57A7C203LL;
    int32_t l_18 = 1L;
    if ((safe_mod_func_int64_t_s_s(l_4, 0x070ADE2167FA5C62LL)))
    { 
        int32_t l_17 = 0xC3A065C2L;
        g_6 = ((g_5 ^ g_5) < g_5);
        l_18 |= (safe_mod_func_int32_t_s_s(((((g_9--) == (safe_sub_func_uint8_t_u_u((--g_14), 0xE0L))) , l_17) | 0x823AAF5BL), g_5));
        g_19 = g_5;
    }
    else
    { 
        int32_t l_30 = 2L;
        int32_t l_31 = (-10L);
        l_31 = (safe_add_func_uint16_t_u_u((safe_div_func_uint16_t_u_u(((!(safe_mod_func_uint16_t_u_u(((safe_lshift_func_int16_t_s_u(l_4, l_18)) , 0x01EBL), g_29))) && g_5), 1L)), l_30));
    }
    l_18 = 0x5205300CL;
    return g_14;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_29, "g_29", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
