#include "cerberus.h"
/* PR rtl-optimization/17099 */


void
check (int a)
{
  if (a != 1)
    abort ();
}

void
test (int a, int b)
{
  check ((a ? 1 : 0) | (b ? 2 : 0));
}

int
main (void)
{
  test (1, 0);
  exit (0);
}
