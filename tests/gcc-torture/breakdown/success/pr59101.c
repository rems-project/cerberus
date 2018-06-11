#include "cerberus.h"
/* PR target/59101 */

 int
foo (int a)
{
  return (~a & 4102790424LL) > 0 | 6;
}

int 
main (void)
{
  if (foo (0) != 7)
    __builtin_abort ();
  return 0;
}
