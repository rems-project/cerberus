#include "cerberus.h"
int foo(int i)
{
  return ((int)((unsigned)(i + 1) * 4)) / 4;
}

int 
main (void)
{
  if (foo(0x3fffffff) != 0)
    abort ();
  return 0;
}
