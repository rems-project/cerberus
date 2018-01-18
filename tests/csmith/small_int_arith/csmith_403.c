// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_403.c
#include "csmith.h"


static long __undefined;



static int16_t g_2 = 2L;
static int16_t g_3 = 0L;
static uint64_t g_6 = 0xD4210E164CAF14C9LL;
static int64_t g_8 = 1L;
static uint8_t g_9 = 0x73L;
static int32_t g_10 = 0x51AF7F3EL;
static int32_t g_14 = (-1L);
static int8_t g_15 = (-1L);
static int64_t g_16 = 0x4157736D0C11E043LL;
static int64_t g_19 = 0L;
static uint8_t g_21 = 250UL;
static int8_t g_25 = 0x3AL;



static uint16_t  func_1(void);




static uint16_t  func_1(void)
{ 
    const uint32_t l_7 = 0xB471DFD9L;
    int32_t l_18 = 0xF0DFBC43L;
    int32_t l_20 = 0x31E13CA4L;
    g_3 ^= g_2;
    for (g_3 = 0; (g_3 <= 5); g_3 = safe_add_func_int16_t_s_s(g_3, 6))
    { 
        g_6 &= 0x1E948708L;
        g_8 &= l_7;
        g_9 = g_3;
        g_10 = 0x047D2038L;
    }
    g_10 = (-1L);
    for (g_10 = 0; (g_10 != (-13)); --g_10)
    { 
        int64_t l_13 = (-1L);
        int32_t l_17 = 0x668451F1L;
        int32_t l_24 = 0xC9D94031L;
        l_13 = 0x956E74E8L;
        --g_21;
        return l_24;
    }
    return g_25;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    transparent_crc(g_15, "g_15", print_hash_value);
    transparent_crc(g_16, "g_16", print_hash_value);
    transparent_crc(g_19, "g_19", print_hash_value);
    transparent_crc(g_21, "g_21", print_hash_value);
    transparent_crc(g_25, "g_25", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
