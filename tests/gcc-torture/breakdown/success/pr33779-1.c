#include "cerberus.h"
int foo(int i)
{
  if (((unsigned)(i + 1)) * 4 == 0)
    return 1;
  return 0;
}

int 
main (void)
{
  if (foo(0x3fffffff) == 0)
    abort ();
  return 0;
}
