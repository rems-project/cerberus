// This test checks the typing of the GNU extension E1 ?: E3.
// main returns a bitmask of the failed checks (0: all pass).
int main(void)
{
  int fails = 0, a, *p = &a, *null = 0;
  unsigned char c = 200; long l = 5; int i = 3; double d = 0.5;
  // usual arithmetic conversions of E1 and E3; E1's value converted
  if (_Generic(c ?: l, long: 0, default: 1) || (c ?: l) != 200
    || _Generic(i ?: d, double: 0, default: 1) || (i ?: d) != 3.0 || (d ?: i) != 0.5)
      fails |= 1;
  // a pointer and a null pointer constant
  if ((p ?: 0) != &a || (null ?: p) != &a) fails |= 2;
  return fails;
}
