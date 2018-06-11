#include "cerberus.h"
int 
f (void)
{
  unsigned b = 0;

  if (b > ~0U)
    b = ~0U;

  return b;
}
int 
main (void)
{
  if (f()!=0)
    abort();
  exit (0);
}
