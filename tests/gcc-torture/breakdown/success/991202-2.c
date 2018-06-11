#include "cerberus.h"

int 
f1 (void)
{
  unsigned long x, y = 1;

  x = ((y * 8192) - 216) % 16;
  return x;
}

int 
main (void)
{
  if (f1 () != 8)
    abort ();
  exit (0);
}
