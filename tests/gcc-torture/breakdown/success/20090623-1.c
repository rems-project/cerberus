#include "cerberus.h"
int * __restrict__ x;

int foo (int y)
{
  *x = y;
  return *x;
}


int 
main (void)
{
  int i = 0;
  x = &i;
  if (foo(1) != 1)
    abort ();
  return 0;
}
