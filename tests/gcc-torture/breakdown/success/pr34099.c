#include "cerberus.h"
int foo (int b, int c)
{
  int x;
  if (b)
    return x & c;
  else
    return 1;
}
int 
main (void)
{
  if (foo(1, 0) != 0)
    abort ();
  return 0;
}

