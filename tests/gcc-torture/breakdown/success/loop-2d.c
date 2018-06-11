#include "cerberus.h"
int a[2];

void
f (int b)
{
  unsigned int i;
  int *p;
  for (p = &a[b], i = b; --i < ~0; )
    *--p = i * 3 + (int)a;
}

int 
main (void)
{
  a[0] = a[1] = 0;
  f (2);
  if (a[0] != (int)a || a[1] != (int)a + 3)
    abort ();
  exit (0);
}
