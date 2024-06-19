

int
f (void)
{
  unsigned int x = 1;
  unsigned int y;

  y = __builtin_ffs(x);
  /*@ assert (y == 1u32); @*/

  y = __builtin_ctz(x);
  /*@ assert (y == 0u32); @*/

  x *= 2;
  y = __builtin_ctz(x);
  /*@ assert (y == 1u32); @*/

  return 1;
}

int main(void)
/*@ trusted; @*/
{
  int r = f();
}
