// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_616.c
#include "csmith.h"


static long __undefined;



static int8_t g_2 = (-1L);
static int32_t g_8 = 5L;
static int16_t g_9 = (-5L);
static int32_t g_10 = 1L;
static uint16_t g_12 = 0xE32CL;
static int16_t g_23 = 0x8CA8L;
static uint32_t g_28 = 4294967295UL;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint32_t l_3 = 18446744073709551615UL;
    int32_t l_4 = 0x74DD0324L;
    int32_t l_5 = 1L;
    int32_t l_6 = 1L;
    uint32_t l_17 = 0UL;
    int16_t l_20 = 0x197EL;
    uint8_t l_32 = 250UL;
    if (g_2)
    { 
        int64_t l_7 = 0L;
        int32_t l_11 = 0xE17B844AL;
        l_3 = g_2;
        ++g_12;
        if (g_2)
            goto lbl_16;
        g_10 = g_10;
    }
    else
    { 
        uint8_t l_15 = 255UL;
        l_15 = g_8;
        return l_4;
    }
    if (l_5)
    { 
lbl_16:
        g_8 = 0x14CD4959L;
        l_17 = g_2;
    }
    else
    { 
        uint32_t l_18 = 0x946B43D2L;
        int32_t l_19 = (-1L);
        l_19 |= l_18;
        g_8 = l_20;
        l_19 = 0L;
    }
    if (l_4)
    { 
        int32_t l_21 = 1L;
        int32_t l_22 = 0x5051DD2EL;
        int32_t l_24 = 0x758FC567L;
        int32_t l_25 = 0x8FAD7494L;
        int32_t l_26 = 0x3747C914L;
        int32_t l_27 = 0x49C4B05EL;
        l_5 |= 5L;
        g_8 = 1L;
        --g_28;
    }
    else
    { 
        int64_t l_31 = 2L;
        l_32 = l_31;
        return g_12;
    }
    if (g_28)
    { 
        int8_t l_33 = 0L;
        l_33 |= 0x8BA79672L;
        return l_33;
    }
    else
    { 
        const uint16_t l_34 = 65533UL;
        g_10 = l_34;
        g_10 = g_8;
    }
    return l_5;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    transparent_crc(g_12, "g_12", print_hash_value);
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_28, "g_28", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
