#include "cerberus.h"
void
f (unsigned n)
{
  if ((int) n >= 0)
    abort ();
}

int 
main (void)
{
  unsigned x = ~0;
  f (x);
  exit (0);
}
