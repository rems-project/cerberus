#include "cerberus.h"
int i, a[99];

void f (int one)
{
  if (one != 1)
    abort ();
}

void 
g (void)
{
  f (a[i & 0x3f]);
}

int 
main (void)
{
  a[0] = 1;
  i = 0x40;
  g ();
  exit (0);
}
