#include "cerberus.h"
float 
fx (double x)
{
  return 1.0 + 3.0 / (2.302585093 * x);
}

float 
inita (void) { return 3.0; }
float 
initc (void) { return 4.0; }
void
f (void) {}

int 
main (void)
{
  float fx (double), inita (), initc (), a, b, c;
  a = inita ();
  c = initc ();
  f ();
  b = fx (c) + a;
  f ();
  if (a != 3.0 || b < 4.3257 || b > 4.3258 || c != 4.0)
    abort ();
  exit (0);
}

