#include "cerberus.h"
int foo (int i)
{
  return -2 * __builtin_abs(i - 2);
}
int 
main (void)
{
  if (foo(1) != -2
      || foo(3) != -2)
    abort ();
  return 0;
}
