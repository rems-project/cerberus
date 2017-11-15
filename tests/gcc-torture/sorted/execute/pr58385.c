#include "cerberus.h"
/* PR tree-optimization/58385 */


int a, b = 1;

int
foo ()
{
  b = 0;
  return 0;
}

int
main ()
{
  ((0 || a) & foo () >= 0) <= 1 && 1;
  if (b)
    abort ();
  return 0;
}
