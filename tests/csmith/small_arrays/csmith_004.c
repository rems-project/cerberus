// Options:   --arrays --no-bitfields --checksum --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --safe-math --no-packed-struct --no-pointers --no-structs --no-unions --no-volatiles --no-volatile-pointers --no-const-pointers --concise
#include "csmith.h"


static long __undefined;



static int32_t g_3 = 0x61F66568L;
static int64_t g_6[4][9] = {{0x47941CE3CB5AF9F7LL,0x72B5725D36729694LL,0xC45C1D102278213ALL,0x72B5725D36729694LL,0x47941CE3CB5AF9F7LL,1L,0xB35EDADE0980DB95LL,0xE6E7F737A9A97186LL,(-7L)},{0x86BA47C9D5FAC122LL,0x72B5725D36729694LL,1L,(-7L),1L,0x990069F30CC2FDCBLL,(-7L),0x990069F30CC2FDCBLL,1L},{0xB35EDADE0980DB95LL,1L,1L,0xB35EDADE0980DB95LL,0xF7919ADB821342F3LL,1L,0xC45C1D102278213ALL,(-7L),(-3L)},{0xB35EDADE0980DB95LL,(-1L),0x76AB2AEE5A9864BALL,1L,(-3L),0xF7919ADB821342F3LL,0xF7919ADB821342F3LL,(-3L),1L}};
static int32_t g_7 = (-7L);
static uint64_t g_8[3] = {0x9C23EDB39523DD97LL,0x9C23EDB39523DD97LL,0x9C23EDB39523DD97LL};



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    int16_t l_2 = (-6L);
    int8_t l_4 = (-1L);
    int32_t l_5 = 0xC405B401L;
    int16_t l_14 = 6L;
    l_2 &= 0x62D5E48DL;
    g_8[0]--;
    if (((0x595AD338L | 0xB76E1EE6L) | g_8[0]))
    { 
        uint64_t l_11 = 18446744073709551614UL;
        l_11--;
    }
    else
    { 
        return l_4;
    }
    return l_14;
}





int main (int argc, char* argv[])
{
    int i, j;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_3, "g_3", print_hash_value);
    for (i = 0; i < 4; i++)
    {
        for (j = 0; j < 9; j++)
        {
            transparent_crc(g_6[i][j], "g_6[i][j]", print_hash_value);
            if (print_hash_value) printf("index = [%d][%d]\n", i, j);

        }
    }
    transparent_crc(g_7, "g_7", print_hash_value);
    for (i = 0; i < 3; i++)
    {
        transparent_crc(g_8[i], "g_8[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
