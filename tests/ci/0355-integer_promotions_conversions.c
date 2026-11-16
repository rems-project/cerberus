// Integer promotions (§6.3.1.1#2) and usual arithmetic conversions (§6.3.1.8#1),
// including the types Cerberus models with dedicated variants (size_t, ptrdiff_t,
// wchar_t, (u)intptr_t, (u)intmax_t) and enumerated types. Assumes the default
// implementation (LP64, signed char, size_t = unsigned long, ptrdiff_t = intptr_t
// = intmax_t = long, wchar_t = int).
// Returns the line of the first failing check, 0 if none.
#include <stddef.h>
#include <stdint.h>
#include <limits.h>

#define TEST(e, T, v)                                    \
  if (!_Generic((e), T: 1, default: 0) || (e) != (T)(v)) \
    return __LINE__;

enum E { E_NEG = -1, E_POS = 1 };
enum U { U_ONE = 1 };

int main(void)
{
  _Bool b = 1;
  char c = -1;
  unsigned char uc = 255;
  short s = -1;
  unsigned short us = 65535;
  unsigned u = 1;
  long l = -1;
  unsigned long ul = 0;
  long long ll = -1;
  enum E e = E_NEG; enum U eu = U_ONE;
  size_t z = (size_t)1 << 32;
  ptrdiff_t d = -1;
  wchar_t w = 0;
  intptr_t ip = -1;
  uintptr_t up = 1;
  intmax_t im = -1;
  uintmax_t um = 1;

  // integer promotions
  TEST(+b, int, 1)
  TEST(+c, int, -1)
  TEST(~uc, int, -256)
  TEST(-us, int, -65535)
  TEST(+s, int, -1)
  TEST(+e, int, -1)
  TEST(+eu, unsigned, 1)
  TEST(uc << 1, int, 510)
  TEST(us >> 1, int, 32767)
  TEST(+z, size_t, 4294967296)
  TEST(z >> 32, size_t, 1)
  TEST(-d, ptrdiff_t, 1)
  TEST(+w, int, 0)
  TEST(~ip, intptr_t, 0)

  // usual arithmetic conversions
  TEST(b + b, int, 2)
  TEST(uc + us, int, 65790)
  TEST(c + l, long, -2)
  TEST(-1 + u, unsigned, 0)
  TEST(l + u, long, 0)
  TEST(ll + ul, unsigned long long, ULLONG_MAX)
  TEST(u + ll, long long, 0)
  TEST(z + -1, size_t, 4294967295)
  TEST(z > 0, int, 1)
  TEST(z + ll, unsigned long long, 4294967295)
  TEST(d + ul, unsigned long, ULONG_MAX)
  TEST(d + u, long, 0)
  TEST(d < z, int, 0)
  TEST(ip + ul, unsigned long, ULONG_MAX)
  TEST(up + -2, uintptr_t, ULONG_MAX)
  TEST(im + um, uintmax_t, 0)
  TEST(im + 1ull, unsigned long long, 0)
  TEST(w - 1, int, -1)
  TEST(w - 1 + u, unsigned, 0)
  TEST(e + u, unsigned, 0)
  TEST(eu + l, long, 0)
  TEST(1 ? uc : l, long, 255)
  TEST(1 ? z : -1, size_t, 4294967296)
  TEST(0 ? ul : d, unsigned long, ULONG_MAX)

  // ranges of the dedicated variants
  TEST((wchar_t)-1 < 0, int, 1)
  TEST(WCHAR_MIN < 0, int, 1)
  TEST(SIZE_MAX == ULONG_MAX, int, 1)
}
