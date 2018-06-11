#include "cerberus.h"
/* Verify that we do not lose side effects on a MOD expression.  */


int
foo (int a)
{
  int x = 0 % a++;
  return a;
}

int 
main (void)
{
  if (foo (9) != 10)
    abort ();
  exit (0);
}
