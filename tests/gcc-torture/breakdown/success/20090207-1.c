#include "cerberus.h"
int foo(int i)
{
  int a[32];
  a[1] = 3;
  a[0] = 1;
  a[i] = 2;
  return a[0];
}
int 
main (void)
{
  if (foo (0) != 2
      || foo (1) != 1)
    abort ();
  return 0;
}
