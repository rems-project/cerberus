#include "cerberus.h"
double glob_dbl;

void
f (double *pdbl, double value)
{
  if (pdbl == 0)
    pdbl = &glob_dbl;

  *pdbl = value;
}

int 
main (void)
{
  f ((void *) 0, 55.1);

  if (glob_dbl != 55.1)
    abort ();
  exit (0);
}
