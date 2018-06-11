#include "cerberus.h"
/* PR rtl-optimization/64255 */

 void
bar (long i, unsigned long j)
{
  if (i != 1 || j != 1)
    __builtin_abort ();
}

 void
foo (long i)
{
  unsigned long j;

  if (!i)
    return;
  j = i >= 0 ? (unsigned long) i : - (unsigned long) i;
  if ((i >= 0 ? (unsigned long) i : - (unsigned long) i) != j)
    __builtin_abort ();
  bar (i, j);
}

int 
main (void)
{
  foo (1);
  return 0;
}
