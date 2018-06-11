#include "cerberus.h"
void
f (int x, int y)
{
  if (x % y != 0)
    abort ();
}

int 
main (void)
{
  f (-5, 5);
  exit (0);
}
