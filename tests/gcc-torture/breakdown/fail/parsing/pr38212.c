#include "cerberus.h"
int 
foo (int *__restrict p, int i)
{
  int *__restrict q;
  int *__restrict r;
  int v, w;
  q = p + 1;
  r = q - i;
  v = *r;
  *p = 1;
  w = *r;
  return v + w;
}
int 
main (void)
{
  int i = 0;
  if (foo (&i, 1) != 1)
    abort ();
  return 0;
}

