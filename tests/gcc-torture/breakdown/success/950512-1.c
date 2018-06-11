#include "cerberus.h"
unsigned 
f1 (int x)
{
  return ((unsigned) (x != 0) - 3) / 2;
}

unsigned long long 
f2 (int x)
{
  return ((unsigned long long) (x != 0) - 3) / 2;
}

int 
main (void)
{
  if (f1 (1) != (~(unsigned) 0) >> 1)
    abort ();
  if (f1 (0) != ((~(unsigned) 0) >> 1) - 1)
    abort ();
  if (f2 (1) != (~(unsigned long long) 0) >> 1)
    abort ();
  if (f2 (0) != ((~(unsigned long long) 0) >> 1) - 1)
    abort ();
  exit (0);
}
