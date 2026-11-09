// This test checks the elaboration of the GNU extension E1 ?: E3.
// main returns a bitmask of the failed checks (0: all pass).
static int n; // number of operand evaluations
static int t(int v) { n++; return v; }
static int *tp(int *p) { n++; return p; }

int main(void)
{
  int fails = 0, x, a, b;
  int *p = &a, *null = 0;

  // E1 != 0: the result is E1's value (not 1), E1 evaluated once,
  // E3 not evaluated
  n = 0; if ((t(2) ?: t(7)) != 2 || n != 1) fails |= 1;
  // E1 == 0: E1 and E3 evaluated once each, the result is E3
  n = 0; if ((t(0) ?: t(7)) != 7 || n != 2) fails |= 2;
  // a pointer E1 (compared with a null pointer): evaluated once
  n = 0; if ((tp(p) ?: &b) != &a || n != 1) fails |= 4;
  n = 0; if ((tp(null) ?: tp(&b)) != &b || n != 2) fails |= 8;
  // there is a sequence point between E1 and E3
  x = 0; if (((x++, 0) ?: x) != 1) fails |= 16;
  // right associative: E1 ?: (E2 ?: E3)
  if ((0 ?: 0 ?: 4) != 4 || (5 ?: t(0) ?: 4) != 5) fails |= 32;
  return fails;
}
