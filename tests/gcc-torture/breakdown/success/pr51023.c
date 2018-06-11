#include "cerberus.h"
/* PR rtl-optimization/51023 */


short int
foo (long int x)
{
  return x;
}

int 
main (void)
{
  long int a = 0x4272AL;
  if (foo (a) == a)
    abort ();
  return 0;
}
