#include "cerberus.h"
int 
ffs (int x)
{
  int bit, mask;

  if (x == 0)
    return 0;

  for (bit = 1, mask = 1; !(x & mask); bit++, mask <<= 1)
    ;

  return bit;
}

void 
f (int x)
{
  int y;
  y = ffs (x) - 1;
  if (y < 0) 
    abort ();
}

int 
main (void)
{
  f (1);
  exit (0);
}
