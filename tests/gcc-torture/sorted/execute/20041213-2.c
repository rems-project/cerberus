#include "cerberus.h"
/* PR tree-optimization/18694

   The dominator optimization didn't take the PHI evaluation order
   into account when threading an edge.  */


void __attribute__((noinline))
foo (int i)
{
  int next_n = 1;
  int j = 0;

  for (; i != 0; i--)
    {
      int n;

      for (n = next_n; j < n; j++)
	next_n++;

      if (j != n)
	abort ();
    }
}

int
main (void)
{
  foo (2);
  exit (0);
}
