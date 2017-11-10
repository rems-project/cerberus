// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_1138.c
#include "csmith.h"


static long __undefined;



static uint64_t g_5 = 0xEAFD94FE5F36F6DDLL;
static int16_t g_10 = 3L;
static int64_t g_12 = 0xEF989B1AB4456E34LL;
static uint16_t g_13 = 0x45B0L;
static int64_t g_14 = 0xB0AE28DE637C5B15LL;



static int16_t  func_1(void);




static int16_t  func_1(void)
{ 
    uint16_t l_2 = 0x1BF5L;
    uint64_t l_8 = 0x3D1BCA9D6923607ALL;
    int32_t l_11 = 2L;
    g_13 = ((g_5 = (0x94L ^ (++l_2))) ^ (safe_mod_func_uint16_t_u_u(l_8, (((((l_11 = (~(g_10 = 0x38L))) , g_10) < g_12) | g_12) , g_10))));
    g_14 = g_5;
    return l_11;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
