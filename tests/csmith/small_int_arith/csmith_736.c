// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_736.c
#include "csmith.h"


static long __undefined;



static uint32_t g_4 = 0x6E871D97L;
static uint64_t g_8 = 0xB5CA9869EC4279C4LL;
static uint64_t g_9 = 0x0BE39E3CF95751CFLL;
static int8_t g_10 = (-1L);



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int32_t l_2 = 0xB642C70BL;
    int32_t l_3 = (-7L);
    g_4--;
    if (g_4)
        goto lbl_11;
    if (g_4)
    { 
        uint8_t l_7 = 0x80L;
        g_8 = l_7;
    }
    else
    { 
        g_9 &= g_4;
        g_10 |= 0x6673E7EDL;
    }
lbl_11:
    l_3 ^= g_8;
    for (l_2 = (-23); (l_2 < (-25)); l_2 = safe_sub_func_uint64_t_u_u(l_2, 5))
    { 
        l_3 &= 0L;
    }
    return g_10;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
