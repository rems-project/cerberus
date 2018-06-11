#include "cerberus.h"
char *a = 0;
char *b = 0;

void
g (int x)
{
  if ((!!a) != (!!b))
    abort ();
}

void
f (int x)
{
  g (x * x);
}

int 
main (void)
{
  f (100);
  exit (0);
}
