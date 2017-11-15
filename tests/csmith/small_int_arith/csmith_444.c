// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_444.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2 = 0x847DL;
static uint32_t g_13 = 0UL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int32_t l_3 = 0x4FFB871CL;
    int32_t l_6 = 0x5043C4ABL;
    uint32_t l_7 = 0xF27D2703L;
    int32_t l_12 = 0xA26F3F17L;
    l_3 = g_2;
    for (l_3 = (-26); (l_3 <= (-27)); l_3 = safe_sub_func_uint16_t_u_u(l_3, 1))
    { 
        l_6 = g_2;
        l_6 = g_2;
        if (l_6)
            break;
        if (l_6)
            continue;
    }
    --l_7;
    for (l_3 = (-15); (l_3 != (-5)); l_3 = safe_add_func_uint32_t_u_u(l_3, 1))
    { 
        --g_13;
        return g_2;
    }
    return g_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
