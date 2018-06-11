#include "cerberus.h"
f (signed long long int x)
{
  return x > 0xFFFFFFFFLL || x < -0x80000000LL;
}

int 
main (void)
{
  if (f (0) != 0)
    abort ();
  exit (0);
}
