#include "cerberus.h"
/* PR target/49281 */


 int
foo (int x)
{
  return (x << 2) | 4;
}

 int
bar (int x)
{
  return (x << 2) | 3;
}

int 
main (void)
{
  if (foo (43) != 172 || foo (1) != 4 || foo (2) != 12)
    abort ();
  if (bar (43) != 175 || bar (1) != 7 || bar (2) != 11)
    abort ();
  return 0;
}
