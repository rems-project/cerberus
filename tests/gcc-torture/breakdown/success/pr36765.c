#include "cerberus.h"
int 
foo(int i)
{
  int *p = __builtin_malloc (4 * sizeof(int));
  *p = 0;
  p[i] = 1;
  return *p;
}
int 
main (void)
{
  if (foo(0) != 1)
    abort ();
  return 0;
}
