#include "cerberus.h"
int glob;

int 
g (int x)
{
  glob = x;
  return 0;
}

void
f (int x)
{
  int a = ~x;
  while (a)
    a = g (a);
}

int 
main (void)
{
  f (3);
  if (glob != -4)
    abort ();
  exit (0);
}
