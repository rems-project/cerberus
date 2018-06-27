#include "cerberus.h"
void
f (int i)
{
  if (((1 << i) & 1) == 0)
    abort ();
}

int 
main (void)
{
  f (0);
  exit (0);
}
