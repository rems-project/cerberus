#include "cerberus.h"
int 
f (int x)
{
  if (x != 0 || x == 0)
    return 0;
  return 1;
}

int 
main (void)
{
  if (f (3))
    abort ();
  exit (0);
}
