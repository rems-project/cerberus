#include "cerberus.h"
/* PR 8639.  */


int foo (int i)
{
  int r;
  r = (80 - 4 * i) / 20;
  return r;
}
    
int 
main (void)
{
  if (foo (1) != 3)
    abort ();
  return 0;
}
