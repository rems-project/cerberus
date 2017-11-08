// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_946.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xB110C93BL;
static int32_t g_12 = (-1L);
static uint32_t g_13 = 0x1ADB2BC4L;



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    uint16_t l_9 = 0xCB8CL;
    int32_t l_10 = 0xDA622A14L;
    int32_t l_11 = 0x672CA3C0L;
    for (g_2 = 0; (g_2 <= (-8)); g_2--)
    { 
        int16_t l_5 = 0L;
        uint32_t l_6 = 0x07E17F75L;
        ++l_6;
    }
    g_2 = l_9;
    g_13--;
    return l_10;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
