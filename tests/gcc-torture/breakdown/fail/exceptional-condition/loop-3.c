#include "cerberus.h"

int n = 0;

int 
g (int i)
{
  n++;
}

int 
f (int m)
{
  int i;
  i = m;
  do
    {
      g (i * INT_MAX / 2);
    }
  while (--i > 0);
}

int 
main (void)
{
  f (4);
  if (n != 4)
    abort ();
  exit (0);
}
