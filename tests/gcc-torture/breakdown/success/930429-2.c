#include "cerberus.h"
int 
f (int b)
{
  return (b >> 1) > 0;
}

int 
main (void)
{
  if (!f (9))
    abort ();
  if (f (-9))
    abort ();
  exit (0);
}
