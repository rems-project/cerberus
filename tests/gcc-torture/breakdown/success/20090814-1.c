#include "cerberus.h"
int 
bar (int *a)
{
  return *a;
}
int i;
int 
foo (int (*a)[2])
{
  return bar (&(*a)[i]);
}

int a[2];
int 
main (void)
{
  a[0] = -1;
  a[1] = 42;
  i = 1;
  if (foo (&a) != 42)
    abort ();
  return 0;
}
