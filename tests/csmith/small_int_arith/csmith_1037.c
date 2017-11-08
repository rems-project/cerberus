// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1037.c
#include "csmith.h"


static long __undefined;



static uint64_t g_2 = 1UL;
static int32_t g_5 = 0xBA22E974L;
static int64_t g_6 = 0x34111D0188753E1ELL;
static int16_t g_7 = (-1L);
static int8_t g_9 = (-6L);
static uint16_t g_10 = 0x5BC4L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int8_t l_3 = 0x85L;
    int32_t l_4 = (-1L);
    int32_t l_8 = (-3L);
    int8_t l_13 = 7L;
    g_5 = ((((l_4 = (((((g_2 && (g_2 >= (0UL < l_3))) , g_2) , g_2) == g_2) < g_2)) == g_2) <= g_2) != g_2);
    --g_10;
    return l_13;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
