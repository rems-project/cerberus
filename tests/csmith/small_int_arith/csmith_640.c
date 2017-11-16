// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_640.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x1928C176L;
static int64_t g_6 = 0x849F845D811F07B4LL;



static const int32_t  func_1(void);




static const int32_t  func_1(void)
{ 
    uint8_t l_7 = 0UL;
    int32_t l_10 = 0x7D50F82BL;
    for (g_2 = 0; (g_2 <= (-26)); g_2--)
    { 
        int32_t l_5 = 0x70C3099CL;
        if (l_5)
            break;
    }
    g_6 ^= g_2;
    if (l_7)
    { 
        const int64_t l_8 = 0L;
        return l_8;
    }
    else
    { 
        uint8_t l_9 = 0x0DL;
        g_2 = l_9;
    }
    l_10 = l_7;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
