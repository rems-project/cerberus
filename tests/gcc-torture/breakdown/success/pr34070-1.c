#include "cerberus.h"

int f(unsigned int x)
{
    return ((int)x) % 4;
}

int 
main (void)
{
  if (f(-1) != -1)
    abort ();
  return 0;
}
