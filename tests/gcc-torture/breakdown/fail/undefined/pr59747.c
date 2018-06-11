#include "cerberus.h"

int a[6], c = 1, d;
short e;

int 
fn1 (int p)
{
  return a[p];
}

int 
main (void)
{
  if (sizeof (long long) != 8)
    exit (0);

  a[0] = 1;
  if (c)
    e--;
  d = e;
  long long f = e;
  if (fn1 ((f >> 56) & 1) != 0)
    abort ();
  exit (0);
}
