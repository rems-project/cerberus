#include "cerberus.h"
/* PR tree-optimization/46909 */


int

foo (unsigned int x)
{
  if (! (x == 4 || x == 6) || (x == 2 || x == 6))
    return 1;
  return -1;
}

int 
main (void)
{
  int i;
  for (i = -10; i < 10; i++)
    if (foo (i) != 1 - 2 * (i == 4))
      abort ();
  return 0;
}
