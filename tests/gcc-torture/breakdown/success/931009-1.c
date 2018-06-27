#include "cerberus.h"
void f(void);
int
main (void)
{
  f ();
  exit (0);
}

static void
g (int *out, int size, int lo, int hi)
{
  int j;

  for (j = 0; j < size; j++)
    out[j] = j * (hi - lo);
}


void
f (void)
{
  int a[2];

  g (a, 2, 0, 1);

  if (a[0] != 0 || a[1] != 1)
    abort ();
}
