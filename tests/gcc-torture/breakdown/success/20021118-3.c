#include "cerberus.h"

int
foo (int x)
{
  if (x == -2 || -x - 100 >= 0)
    abort ();
  return 0;
}
           
int 
main (void)
{
  foo (-3);
  foo (-99);
  exit (0);
}
