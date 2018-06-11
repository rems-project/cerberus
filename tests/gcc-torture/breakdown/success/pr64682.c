#include "cerberus.h"
/* PR rtl-optimization/64682 */

int a, b = 1;

 void
foo (int x)
{
  if (x != 5)
    __builtin_abort ();
}

int 
main (void)
{
  int i;
  for (i = 0; i < 56; i++)
    for (; a; a--)
      ;
  int *c = &b;
  if (*c)
    *c = 1 % (unsigned int) *c | 5;

  foo (b);

  return 0;
}
