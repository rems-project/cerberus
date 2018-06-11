#include "cerberus.h"
static double one = 1.0;

int 
f (void)
{
  int colinear;
  colinear = (one == 0.0);
  if (colinear)
    abort ();
  return colinear;
}
int 
main (void)
{
  if (f()) abort();
  exit (0);
}
