#include "cerberus.h"
struct Foo {
  int *p;
  int *q;
};

void 
bar (int **x)
{
  struct Foo *f = (struct Foo *)x;
  *(f->q) = 0;
}

int foo(void)
{
  struct Foo f;
  int i = 1, j = 2;
  f.p = &i;
  f.q = &j;
  bar(&f.p);
  return j;
}

int 
main (void)
{
  if (foo () != 0)
    abort ();
  return 0;
}
