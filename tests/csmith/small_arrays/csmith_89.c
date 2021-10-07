// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_89.c
#include "csmith.h"


static long __undefined;



static uint32_t g_7 = 0xC23AFC37L;
static int32_t g_10 = 0x647C2C9EL;
static int8_t g_13 = 0xB3L;
static int32_t g_16 = 0x46E33A79L;
static int64_t g_18[3] = {0x7A140552487223B1LL,0x7A140552487223B1LL,0x7A140552487223B1LL};



static uint64_t  func_1(void);




static uint64_t  func_1(void)
{ 
    int32_t l_6 = 0xACCBAD86L;
    uint16_t l_8 = 4UL;
    int32_t l_9 = 0L;
    int32_t l_11 = 3L;
    int32_t l_12 = 0L;
    int32_t l_14 = 0x5D5F8D9AL;
    int32_t l_15 = (-1L);
    int32_t l_17 = 0x56718E50L;
    uint8_t l_19 = 0x53L;
    g_10 ^= (((safe_add_func_uint8_t_u_u(((l_9 |= ((safe_mod_func_int16_t_s_s(l_6, g_7)) , ((l_6 , l_8) , 0L))) | l_6), g_7)) , 0UL) != 0x79F6A715L);
    ++l_19;
    return l_14;
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_7, "g_7", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_13, "g_13", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    for (i = 0; i < 3; i++)
    {
        transparent_crc(g_18[i], "g_18[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
