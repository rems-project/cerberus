#include "cerberus.h"
/* PR 8848 */


int foo(int status)
{
  int s = 0;
  if (status == 1) s=1;
  if (status == 3) s=3;
  if (status == 4) s=4;
  return s;
}

int 
main (void)
{
  if (foo (3) != 3)
    abort ();
  return 0;
}
