// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_126.c
#include "csmith.h"


static long __undefined;



static uint16_t g_2[2] = {0x9F9BL,0x9F9BL};
static int32_t g_3 = 0x905C8094L;
static uint8_t g_4 = 0xCEL;
static int16_t g_10 = 0xDDA3L;
static int32_t g_21[1] = {8L};
static int8_t g_23 = 0xA3L;
static uint64_t g_27 = 0x74BDBAF9EB11DE2ALL;



static int32_t  func_1(void);




static int32_t  func_1(void)
{ 
    const uint64_t l_13 = 0x1AB4456E348CC383LL;
    int32_t l_14 = 0xCA968364L;
    int32_t l_17 = 7L;
    uint16_t l_18[2];
    int32_t l_25 = (-1L);
    int i;
    for (i = 0; i < 2; i++)
        l_18[i] = 0x5DEAL;
    for (g_3 = 1; (g_3 >= 0); g_3 -= 1)
    { 
        int32_t l_9 = 0xD6923607L;
        int i;
        g_4--;
        g_10 = ((safe_mod_func_uint16_t_u_u((g_2[g_3] = 0UL), l_9)) ^ ((g_3 > g_3) && g_3));
        l_14 = (safe_rshift_func_int16_t_s_u(l_13, g_2[g_3]));
        l_9 = 0xB0AE28DEL;
        return g_2[g_3];
    }
    for (l_14 = 0; (l_14 >= (-1)); --l_14)
    { 
        int32_t l_22 = (-3L);
        int32_t l_24 = 0x2F617A94L;
        int32_t l_26 = 0x19820B27L;
        l_18[0]--;
        if (g_10)
            continue;
        ++g_27;
        if (g_23)
            break;
    }
    return l_18[0];
}





int main (int argc, char* argv[])
{
    int i;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    for (i = 0; i < 2; i++)
    {
        transparent_crc(g_2[i], "g_2[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_3, "g_3", print_hash_value);
    transparent_crc(g_4, "g_4", print_hash_value);
    transparent_crc(g_10, "g_10", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_21[i], "g_21[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_23, "g_23", print_hash_value);
    transparent_crc(g_27, "g_27", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
