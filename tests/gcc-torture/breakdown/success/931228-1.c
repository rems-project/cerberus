#include "cerberus.h"
int 
f (int x)
{
  x &= 010000;
  x &= 007777;
  x ^= 017777;
  x &= 017770;
  return x;
}

int 
main (void)
{
  if (f (-1) != 017770)
    abort ();
  exit (0);
}
