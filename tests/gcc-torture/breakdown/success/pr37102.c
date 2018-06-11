#include "cerberus.h"

unsigned int a, b = 1, c;

void 
foo (int x)
{
  if (x != 5)
    abort ();
}

int 
main (void)
{
  unsigned int d, e;
  for (d = 1; d < 5; d++)
    if (c)
      a = b;
  a = b;
  e = a << 1;
  if (e)
    e = (e << 1) ^ 1;
  foo (e);
  return 0;
}
