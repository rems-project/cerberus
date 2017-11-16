// Options:   --arrays --no-bitfields --checksum --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --safe-math --no-packed-struct --no-pointers --no-structs --no-unions --no-volatiles --no-volatile-pointers --no-const-pointers --concise
#include "csmith.h"


static long __undefined;



static uint64_t g_8 = 0xBEF7D65121AC4888LL;
static int16_t g_11 = 0xC63CL;
static uint32_t g_12 = 0xF9C25B05L;



static const uint16_t  func_1(void);




static const uint16_t  func_1(void)
{ 
    int16_t l_7 = 0xA9EFL;
    int32_t l_9 = (-10L);
    int32_t l_10 = 0x26EC17E5L;
    l_10 &= (safe_mod_func_int64_t_s_s(((l_9 = (safe_unary_minus_func_uint8_t_u((safe_mod_func_int32_t_s_s((l_7 , 8L), g_8))))) > 0UL), l_7));
    --g_12;
    return l_9;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
