#include "cerberus.h"
/* PR tree-optimization/49039 */
int cnt;

 void
foo (unsigned int x, unsigned int y)
{
  unsigned int minv, maxv;
  if (x == 1 || y == -2U)
    return;
  minv = x < y ? x : y;
  maxv = x > y ? x : y;
  if (minv == 1)
    ++cnt;
  if (maxv == -2U)
    ++cnt;
}

int 
main (void)
{
  foo (-2U, 1);
  if (cnt != 2)
    abort ();
  return 0;
}
