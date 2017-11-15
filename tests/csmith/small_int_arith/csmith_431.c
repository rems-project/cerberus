// Options:   --no-arrays --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 4 --max-expr-complexity 1 --max-funcs 1 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_431.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xA049FE38L;
static int16_t g_5 = (-1L);
static int64_t g_6 = 0x88EB987642760385LL;
static uint32_t g_8 = 7UL;
static int64_t g_11 = 0x74EDF0EBF90350D8LL;
static uint16_t g_14 = 0x5D73L;



static uint8_t  func_1(void);




static uint8_t  func_1(void)
{ 
    uint32_t l_3 = 4UL;
    int32_t l_7 = 4L;
    int64_t l_9 = 0L;
    if (g_2)
    { 
        uint16_t l_4 = 0x0997L;
        l_3 = 0x124F84B8L;
        l_4 |= 1L;
        g_5 = g_2;
        g_6 = 0x74B1B055L;
    }
    else
    { 
        l_7 |= l_3;
        return g_5;
    }
    g_8 ^= 0x67E6AA16L;
    if (l_9)
    { 
        uint64_t l_10 = 0xE19F23E52509E71BLL;
        g_11 = l_10;
        l_7 = g_11;
    }
    else
    { 
        int64_t l_12 = 0x86F25DB2B058EFA9LL;
        int32_t l_13 = (-1L);
        l_13 ^= l_12;
        l_7 = g_8;
        g_14 &= g_6;
        l_7 = 0x37F4A7D2L;
    }
    for (l_3 = 7; (l_3 > 47); l_3 = safe_add_func_uint16_t_u_u(l_3, 4))
    { 
        uint16_t l_17 = 65535UL;
        l_17 = l_7;
        if (l_3)
            break;
    }
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
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_8, "g_8", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
