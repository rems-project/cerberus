#include "cerberus.h"
struct S { float f; };
int 
foo (int *r, struct S *p)
{
  int *q = (int *)&p->f;
  int i = *q;
  *r = 0;
  return i + *q;
}
int 
main (void)
{
  int i = 1;
  if (foo (&i, (struct S *)&i) != 1)
    abort ();
  return (0);
}
