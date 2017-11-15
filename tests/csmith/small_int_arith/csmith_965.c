// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 2 --max-funcs 2 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_965.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2 = 0xC184C506D444182BLL;
static uint64_t g_4 = 0x29949DFCF09CC25FLL;
static int32_t g_7 = 0xABC106ECL;



static int8_t  func_1(void);




static int8_t  func_1(void)
{ 
    int32_t l_3 = 0x7C8A6B95L;
    g_2 ^= 0xC75B57FDL;
    ++g_4;
    g_7 = (g_2 >= l_3);
    return l_3;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
