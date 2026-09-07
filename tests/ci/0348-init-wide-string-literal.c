#include <stdio.h>
#include <stddef.h>
#include <stdint.h>

// STD §6.7.9#15: an array with element type compatible with wchar_t,
// char16_t or char32_t may be initialised by a string literal with the
// corresponding encoding prefix.
//
// NOTE: char16_t/char32_t are spelled here as the types they are defined to
// be (STD §7.28#2), because <uchar.h> is a stub in the bundled libc.

wchar_t unsized[] = L"ab";
wchar_t sized[4] = L"ab";
wchar_t truncated[2] = L"abc";

uint_least16_t u16[] = u"ab";
uint_least32_t u32[] = U"ab";

// UTF-8 literals still initialise a plain character array (§6.7.9#14)
char utf8[] = u8"ab";

// as an inner initialiser
struct S { wchar_t w[3]; int n; };
struct S s = { L"xy", 5 };

int main(void)
{
  printf("unsized[%lu]= {%d, %d, %d}\n",
    sizeof(unsized)/sizeof(wchar_t), (int)unsized[0], (int)unsized[1], (int)unsized[2]);
  printf("sized[%lu]= {%d, %d, %d, %d}\n",
    sizeof(sized)/sizeof(wchar_t),
    (int)sized[0], (int)sized[1], (int)sized[2], (int)sized[3]);
  printf("truncated[%lu]= {%d, %d}\n",
    sizeof(truncated)/sizeof(wchar_t), (int)truncated[0], (int)truncated[1]);
  printf("u16[%lu]= {%d, %d, %d}\n",
    sizeof(u16)/sizeof(uint_least16_t), (int)u16[0], (int)u16[1], (int)u16[2]);
  printf("u32[%lu]= {%d, %d, %d}\n",
    sizeof(u32)/sizeof(uint_least32_t), (int)u32[0], (int)u32[1], (int)u32[2]);
  printf("utf8[%lu]= \"%s\"\n", sizeof(utf8), utf8);
  printf("s= {{%d, %d, %d}, %d}\n",
    (int)s.w[0], (int)s.w[1], (int)s.w[2], s.n);
}
