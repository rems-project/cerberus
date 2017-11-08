// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_576.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = (-5L);
static int32_t g_6 = 1L;
static int64_t g_7 = 1L;
static int16_t g_8 = 0x03D9L;
static int8_t g_9 = 0x53L;
static int8_t g_11 = 0xCAL;
static int16_t g_13 = 0x4C03L;
static uint32_t g_14 = 0x1637C1D6L;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    uint16_t l_3 = 0xB871L;
    int32_t l_10 = 0L;
    int32_t l_12 = 0xA26F3F17L;
    l_3 = g_2;
    for (l_3 = 25; (l_3 >= 17); l_3 = safe_sub_func_uint16_t_u_u(l_3, 4))
    { 
        g_6 = l_3;
        return l_3;
    }
    g_7 = 0x86BD085CL;
    ++g_14;
    return g_8;
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
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
