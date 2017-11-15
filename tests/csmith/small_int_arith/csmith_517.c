// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_517.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = 0x90DAL;
static int8_t g_7 = 7L;
static int64_t g_12 = (-1L);



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint32_t l_4 = 4294967293UL;
    int32_t l_6 = 0xDDD1D8F8L;
    uint8_t l_9 = 0x2DL;
    if (g_2)
    { 
        int32_t l_3 = (-10L);
        l_3 ^= (-9L);
        l_4 = 0xB6182EACL;
    }
    else
    { 
        int64_t l_5 = 8L;
        int32_t l_8 = 0x7516A205L;
        l_6 |= l_5;
        --l_9;
    }
    g_12 = 0xC9C3D069L;
    return l_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
