// This is meant to catch a memory model bug that divides the difference of two
// pointers to arrays by the size of the array's element type rather than by the
// size of the array type.
// Returns the line of the first failing check, 0 if none.
#define TEST(e, v) if ((e) != (v)) return __LINE__;

int main(void)
{
  int a[4][3];
  int b[2][3][4];
  int c[5];
  int (*pc)[5] = &c;
  struct { int x[3]; } s[4];

  TEST((a + 1) - a, 1)
  TEST(&a[0] - &a[3], -3)
  TEST((a + 4) - a, 4)         // one past
  TEST(&b[0][2] - &b[0][0], 2) // the elements are arrays of arrays
  TEST((b + 1) - b, 1)
  TEST((pc + 1) - pc, 1)
  TEST(&a[1][2] - &a[1][0], 2) // not arrays: unchanged
  TEST(&c[4] - &c[1], 3)
  TEST(&s[3] - &s[1], 2)
  return 0;
}
