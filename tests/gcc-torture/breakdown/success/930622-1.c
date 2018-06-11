#include "cerberus.h"
int a = 1, b;

int 
g (void) { return 0; }
int 
h (int x) {}

int 
f (void)
{
  if (g () == -1)
    return 0;
  a = g ();
  if (b >= 1)
    h (a);
  return 0;
}

int 
main (void)
{
  f ();
  if (a != 0)
    abort ();
  exit (0);
}
