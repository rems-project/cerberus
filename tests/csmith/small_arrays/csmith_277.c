// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_277.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0L;
static uint32_t g_10[2] = {4UL,4UL};
static uint8_t g_11 = 0x33L;
static int64_t g_18 = 0xB94D0F4F2301355FLL;
static int32_t g_20 = (-1L);
static int32_t g_23 = 0x7EA4C570L;
static int64_t g_26 = 0x7440271DBCABEBF3LL;
static uint64_t g_28 = 18446744073709551609UL;
static uint8_t g_33 = 0x7FL;



static const int8_t  func_1(void);




static const int8_t  func_1(void)
{ 
    uint8_t l_7 = 0x8FL;
    int32_t l_24 = 0x3F30B91EL;
    int32_t l_25 = 1L;
    int32_t l_27 = 0x6AF9031EL;
    for (g_2 = 9; (g_2 > 21); g_2 = safe_add_func_uint16_t_u_u(g_2, 4))
    { 
        int32_t l_17 = 0xEE39F3FAL;
        int32_t l_19 = 0xAE974CA7L;
        g_10[0] = (safe_mul_func_int8_t_s_s(((l_7 ^ ((safe_sub_func_uint16_t_u_u(0UL, l_7)) == 0x5950707DL)) , (-4L)), 0xFEL));
        g_11--;
        if (l_7)
            continue;
        g_18 = (safe_mul_func_uint8_t_u_u(((+(0x06L != (l_17 , 1L))) == g_2), g_10[0]));
        g_20 = (l_19 = 0x7AF2C9A1L);
        g_23 ^= (safe_add_func_uint8_t_u_u(0xB1L, (g_11 , g_10[1])));
    }
    ++g_28;
    for (g_23 = (-12); (g_23 < 23); g_23 = safe_add_func_int64_t_s_s(g_23, 1))
    { 
        if (l_25)
            break;
        ++g_33;
        if (g_26)
            break;
        if (g_20)
            break;
    }
    for (l_7 = (-17); (l_7 > 36); l_7 = safe_add_func_uint64_t_u_u(l_7, 1))
    { 
        uint32_t l_38 = 4294967292UL;
        l_38--;
    }
    return l_27;
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    for (i = 0; i < 2; i++)
    {
        transparent_crc(g_10[i], "g_10[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_18, "g_18", print_hash_value);
    transparent_crc(g_20, "g_20", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_26, "g_26", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    transparent_crc(g_33, "g_33", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
