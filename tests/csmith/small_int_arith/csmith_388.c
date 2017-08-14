// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_388.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xB110C93BL;
static uint64_t g_6 = 0xC40ED3C15D0D658ELL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    int8_t l_9 = 0x9CL;
    int32_t l_18 = (-5L);
    for (g_2 = (-12); (g_2 > (-9)); g_2 = safe_add_func_int8_t_s_s(g_2, 6))
    { 
        uint8_t l_5 = 255UL;
        int32_t l_10 = 0L;
        l_5 = ((0x7E17F759609C3FBBLL >= g_2) || 0L);
        g_6 = (((0xC0L & g_2) , l_5) && 0xF1L);
        for (l_5 = 0; (l_5 != 21); l_5++)
        { 
            uint64_t l_11 = 0xCE008FB0B44CF592LL;
            if (l_9)
                break;
            --l_11;
            l_10 ^= (safe_sub_func_uint32_t_u_u(0UL, l_11));
        }
    }
    g_2 = (l_18 = (safe_sub_func_uint32_t_u_u(l_9, g_2)));
    g_2 = 0L;
    return l_9;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
