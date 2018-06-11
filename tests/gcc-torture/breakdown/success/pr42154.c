#include "cerberus.h"
struct A { char x[1]; };
void 
foo (struct A a)
{
  if (a.x[0] != 'a')
    abort ();
}
int 
main (void)
{
  struct A a;
  int i;
  for (i = 0; i < 1; ++i)
    a.x[i] = 'a';
  foo (a);
  return 0;
}

