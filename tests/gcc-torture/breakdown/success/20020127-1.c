#include "cerberus.h"
/* This used to fail on h8300.  */


unsigned long
foo (unsigned long n)
{
  return (~n >> 3) & 1;
}

int 
main (void)
{
  if (foo (1 << 3) != 0)
    abort ();

  if (foo (0) != 1)
    abort ();

  exit (0);
}
