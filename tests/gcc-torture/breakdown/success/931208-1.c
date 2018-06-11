#include "cerberus.h"
int 
f (void)
{
  unsigned long x, y = 1;

  x = ((y * 8192) - 216) / 16;
  return x;
}

int 
main (void)
{
  if (f () != 498)
    abort ();
  exit (0);
}
