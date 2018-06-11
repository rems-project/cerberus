#include "cerberus.h"
/* PR tree-optimization/48717 */


int v = 1, w;

unsigned short
foo (unsigned short x, unsigned short y)
{
  return x + y;
}

void
bar (void)
{
  v = foo (~w, w);
}

int 
main (void)
{
  bar ();
  if (v != (unsigned short) -1)
    abort ();
  return 0;
}
