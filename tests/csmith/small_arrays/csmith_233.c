// Options:   --no-pointers --no-structs --no-unions --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 10 --max-expr-complexity 4 --max-funcs 10 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_233.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0xC68EC0AEL;
static int32_t g_6 = (-2L);
static uint8_t g_11 = 5UL;
static uint64_t g_14[1] = {18446744073709551615UL};
static int64_t g_29 = 0x128ABF8B243E5EC3LL;
static int32_t g_36 = 0x9AA50887L;
static int32_t g_37 = 0x1D68C2AFL;
static uint16_t g_39 = 0x7673L;



static uint8_t  func_1(void);
static int32_t  func_19(uint64_t  p_20, int32_t  p_21, uint16_t  p_22);




static uint8_t  func_1(void)
{ 
    uint8_t l_16 = 0xA0L;
    int32_t l_25 = (-1L);
    int32_t l_50 = 0x5FCA44BAL;
    for (g_2 = 0; (g_2 != (-6)); g_2 = safe_sub_func_int16_t_s_s(g_2, 2))
    { 
        uint32_t l_5 = 7UL;
        g_6 ^= (l_5 = g_2);
    }
    for (g_2 = (-6); (g_2 < 17); g_2++)
    { 
        uint64_t l_15 = 9UL;
        g_14[0] = ((safe_mod_func_int64_t_s_s((g_11 = g_6), ((g_6 , (safe_mul_func_uint16_t_u_u(g_2, g_6))) && 0x849B76EEA53061ECLL))) | 3UL);
        l_15 = g_14[0];
    }
    l_16 &= g_6;
    l_50 &= (((l_16 < (safe_sub_func_int32_t_s_s(func_19((safe_mul_func_uint8_t_u_u(g_6, (l_25 = l_16))), l_16, l_16), g_29))) & 0x7762969FBC0AE227LL) | 7UL);
    return g_11;
}



static int32_t  func_19(uint64_t  p_20, int32_t  p_21, uint16_t  p_22)
{ 
    uint8_t l_26 = 0xF4L;
    int32_t l_30 = (-1L);
    int32_t l_31 = 0xBC698DC5L;
    int32_t l_32 = 0x06702E63L;
    int32_t l_33 = 4L;
    int32_t l_34 = 9L;
    int32_t l_35 = 0x87B35F19L;
    int32_t l_38 = 0x68FC786CL;
    int32_t l_42[4];
    uint16_t l_43 = 0xB8F3L;
    int i;
    for (i = 0; i < 4; i++)
        l_42[i] = (-1L);
    --l_26;
    g_39++;
    for (g_2 = 0; (g_2 >= 0); g_2 -= 1)
    { 
        int i;
        return g_14[g_2];
    }
    p_21 = ((l_35 = (l_42[0] != (18446744073709551610UL > l_43))) & 4294967295UL);
    for (l_35 = 0; (l_35 <= 3); l_35 += 1)
    { 
        if (g_14[0])
            break;
        p_21 = ((p_20 < 8L) >= g_14[0]);
        g_36 = (l_32 |= (safe_lshift_func_uint8_t_u_s(p_21, (safe_lshift_func_int16_t_s_s((safe_sub_func_uint16_t_u_u(g_6, p_21)), 4)))));
    }
    return g_39;
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
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_11, "g_11", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_14[i], "g_14[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_29, "g_29", print_hash_value);
    transparent_crc(g_36, "g_36", print_hash_value);
    transparent_crc(g_37, "g_37", print_hash_value);
    transparent_crc(g_39, "g_39", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
