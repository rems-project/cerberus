#include "cerberus.h"
int 
f (unsigned x)
{
  return (unsigned) (((unsigned long long) x * 0xAAAAAAAB) >> 32) >> 1;
}

int 
main (void)
{
  unsigned i;

  for (i = 0; i < 10000; i++)
    if (f (i) != i / 3)
      abort ();
  exit (0);
}
