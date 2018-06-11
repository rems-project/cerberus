#include "cerberus.h"
long 
f (long x, long y)
{
  return (x > 1) ? y : (y & 1);
}

int 
main (void)
{
  if (f (2L, 0xdecadeL) != 0xdecadeL)
    abort ();
  exit (0);
}
