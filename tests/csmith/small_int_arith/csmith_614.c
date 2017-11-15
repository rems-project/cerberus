// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_614.c
#include "csmith.h"


static long __undefined;



static int64_t g_4 = 0x491E29EA41449C9FLL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    uint32_t l_2 = 0xF01C0890L;
    int32_t l_3 = 0x19C5A654L;
    if (l_2)
    { 
        uint64_t l_5 = 1UL;
        l_3 = (-1L);
        l_5 ^= g_4;
    }
    else
    { 
        int32_t l_6 = 0x1DF82D83L;
        l_6 ^= 0L;
    }
    return l_2;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_4, "g_4", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
