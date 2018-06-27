#include "cerberus.h"
int
f(short *p)
{
  short x = *p;
  return (--x < 0);
}

int 
main (void)
{
  short x = -10;
  if (!f(&x))
    abort();
  exit(0);
}
