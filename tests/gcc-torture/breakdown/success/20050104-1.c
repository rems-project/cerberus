#include "cerberus.h"
/* PR tree-optimization/19060 */

static long long 
min (void)
{
  return -__LONG_LONG_MAX__ - 1;
}

void
foo (long long j)
{
  if (j > 10 || j < min ())
    abort ();
}

int
main (void)
{
  foo (10);
  return 0;
}
