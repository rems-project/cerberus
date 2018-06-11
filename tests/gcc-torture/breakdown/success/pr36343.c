#include "cerberus.h"

void 
bar (int **p)
{
  float *q = (float *)p;
  *q = 0.0;
}

float 
foo (int b)
{
  int *i = 0;
  float f = 1.0;
  int **p;
  if (b)
    p = &i;
  else
    p = (int **)&f;
  bar (p);
  if (b)
    return **p;
  return f;
}

int 
main (void)
{
  if (foo(0) != 0.0)
    abort ();
  return 0;
}

