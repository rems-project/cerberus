// Options:   --argc --no-bitfields --checksum --comma-operators --compound-assignment --concise --consts --divs --embedded-assigns --pre-incr-operator --pre-decr-operator --post-incr-operator --post-decr-operator --unary-plus-operator --jumps --longlong --int8 --uint8 --no-float --main --math64 --muls --safe-math --no-packed-struct --no-paranoid --no-volatiles --no-volatile-pointers --const-pointers --no-builtins --max-array-dim 1 --max-array-len-per-dim 4 --max-block-depth 1 --max-block-size 5 --max-expr-complexity 4 --max-funcs 5 --max-pointer-depth 2 --max-struct-fields 2 --max-union-fields 2 -o csmith_2.c
#include "csmith.h"


static long __undefined;



static uint8_t g_5 = 0UL;
static int32_t g_14 = 1L;



static const uint32_t  func_1(void);




static const uint32_t  func_1(void)
{ 
    int64_t l_10 = 0x6B65720B963AB194LL;
    int64_t *l_11 = &l_10;
    uint8_t l_12[4] = {0x32L,0x32L,0x32L,0x32L};
    int32_t *l_13[4] = {(void*)0,(void*)0,(void*)0,(void*)0};
    int i;
    g_14 = (!(g_5 == ((0x248CL == ((safe_add_func_int16_t_s_s((((safe_mod_func_int64_t_s_s(((*l_11) = (0x7D7C1188E17B844ALL >= l_10)), g_5)) && l_12[2]) , g_5), l_12[0])) || 0x98L)) != l_12[2])));
    return g_14;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_5, "g_5", print_hash_value);
    transparent_crc(g_14, "g_14", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
